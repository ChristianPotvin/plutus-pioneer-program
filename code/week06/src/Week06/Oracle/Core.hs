-- Example 1
-- (Oracle Contract - Validator restricts how UTXO can be used)

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Week06.Oracle.Core
    ( Oracle (..)
    , OracleRedeemer (..)
    , oracleTokenName
    , oracleValue
    , oracleAsset
    , oracleInst
    , oracleValidator
    , oracleAddress
    , OracleSchema
    , OracleParams (..)
    , runOracle
    , findOracle
    ) where

import           Control.Monad             hiding (fmap)
import           Data.Aeson                (FromJSON, ToJSON)
import qualified Data.Map                  as Map
import           Data.Monoid               (Last (..))
import           Data.Text                 (Text, pack)
import           GHC.Generics              (Generic)
import           Plutus.Contract           as Contract hiding (when)
import qualified PlutusTx
import           PlutusTx.Prelude          hiding (Semigroup(..), unless)
import           Ledger                    hiding (singleton)
import           Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Ledger.Value              as Value
import           Ledger.Ada                as Ada
import           Plutus.Contracts.Currency as Currency
import           Prelude                   (Semigroup (..))
import qualified Prelude                   as Prelude

-- Parameter for the contract (validator)
data Oracle = Oracle
    { oSymbol   :: !CurrencySymbol
    , oOperator :: !PubKeyHash
    , oFee      :: !Integer
    , oAsset    :: !AssetClass
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

-- Lifts to Plutus code
PlutusTx.makeLift ''Oracle

-- Defines the redeemer (supports "Update" and "Use")
data OracleRedeemer = Update | Use
    deriving Show

-- Raises to Data type 
PlutusTx.unstableMakeIsData ''OracleRedeemer

-- Helpers below...
-- Using "empty" string for the oracle NFT token name.
{-# INLINABLE oracleTokenName #-}
oracleTokenName :: TokenName
oracleTokenName = TokenName emptyByteString

-- Asset of the NFT that is used to identify the oracle value UTXO
{-# INLINABLE oracleAsset #-}
oracleAsset :: Oracle -> AssetClass
oracleAsset oracle = AssetClass (oSymbol oracle, oracleTokenName)

-- Process through which data is extracted from a Datum, from a TxOut
{-# INLINABLE oracleValue #-}
oracleValue :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe Integer
oracleValue o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromData d

{-# INLINABLE mkOracleValidator #-}
-- Parameter -> Datum -> Redeemer -> Context -> Result
mkOracleValidator :: Oracle -> Integer -> OracleRedeemer -> ScriptContext -> Bool
mkOracleValidator oracle x r ctx =
    -- For both Redeemer cases, the below checks apply
    -- Checks that input holds the NFT, and the output that also holds NFT
    traceIfFalse "token missing from input"  inputHasToken  &&
    traceIfFalse "token missing from output" outputHasToken &&
    case r of
        -- Checks for "Update" redeemer
                  -- Checks to make sure the owner signed the transaction
        Update -> traceIfFalse "operator signature missing" (txSignedBy info $ oOperator oracle) &&
                  -- Makes sure the new datum is properly formatted (not Nothing)
                  traceIfFalse "invalid output datum"       validOutputDatum
        -- Allows consumption of the oracle data information
                  -- Ensures value is not being changed
        Use    -> traceIfFalse "oracle value changed"       (outputDatum == Just x)              &&
                  -- Ensures fees are paid up
                  traceIfFalse "fees not paid"              feesPaid
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    -- Checks self for oracle input (should be the NFT)
    ownInput :: TxOut
    -- Returns a Maybe as if we were in a monetary policy script, there is no input
    ownInput = case findOwnInput ctx of
        Nothing -> traceError "oracle input missing"
        Just i  -> txInInfoResolved i

    -- Checks input for specific token (NFT) and makes sure there is only one.
    inputHasToken :: Bool
    inputHasToken = assetClassValueOf (txOutValue ownInput) (oracleAsset oracle) == 1

    ownOutput :: TxOut
    -- 'getCountinuingOutputs' gets a list of all outputs that go to the same script address that is presently being validated
    ownOutput = case getContinuingOutputs ctx of
        [o] -> o     -- Should just be one.
        _   -> traceError "expected exactly one oracle output"

    -- Same as inputHasToken, but checking the output.
    outputHasToken :: Bool
    outputHasToken = assetClassValueOf (txOutValue ownOutput) (oracleAsset oracle) == 1

    -- Retrieves the new value to make sure it's correct.
    outputDatum :: Maybe Integer
    outputDatum = oracleValue ownOutput (`findDatum` info)

    -- Just checks to make sure it's not Nothing.
    validOutputDatum :: Bool
    validOutputDatum = isJust outputDatum

    -- Checks that fees have been paid.
    feesPaid :: Bool
    feesPaid =
      let
        -- Looks at own input (oracle NFT)
        inVal  = txOutValue ownInput
        -- Looks at own output (oracle NFT)
        outVal = txOutValue ownOutput
      in
        -- states that outVal should be greater or equal than inVal with the added expected fees
        outVal `geq` (inVal <> Ada.lovelaceValueOf (oFee oracle))

-- Standard boiler plate.
data Oracling
instance Scripts.ScriptType Oracling where
    -- Defines the DatumType and RedeemerType
    type instance DatumType Oracling = Integer
    type instance RedeemerType Oracling = OracleRedeemer

oracleInst :: Oracle -> Scripts.ScriptInstance Oracling
oracleInst oracle = Scripts.validator @Oracling
    ($$(PlutusTx.compile [|| mkOracleValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode oracle)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @Integer @OracleRedeemer

oracleValidator :: Oracle -> Validator
oracleValidator = Scripts.validatorScript . oracleInst

oracleAddress :: Oracle -> Ledger.Address
oracleAddress = scriptAddress . oracleValidator


-- Off-chain part
-- Handles the start/update
-- Not doing "use", as this is dependant on who wants to use it.

data OracleParams = OracleParams
    { opFees   :: !Integer              -- Fees to charge
    , opSymbol :: !CurrencySymbol       -- CurrencySymbol asset tracked (USD in this case)
    , opToken  :: !TokenName            -- TokenName asset tracked (USD in this case)
    } deriving (Show, Generic, FromJSON, ToJSON)

-- Does not provide the initial value, just mints the NFT.
startOracle :: forall w s. HasBlockchainActions s => OracleParams -> Contract w s Text Oracle
startOracle op = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    -- Uses an existing "forgeContract" to ming the NFT (could have used last weeks code)
    -- mapError converts a Contracts error field into a different error based on a conversion function.
    -- conversion in this case involve 'show' to turn CurrencyError it into a String, and 'pack' to turn it into Text.
    -- (osc - one shot currency)
    osc <- mapError (pack . show) (forgeContract pkh [(oracleTokenName, 1)] :: Contract w s CurrencyError OneShotCurrency)
    let cs     = Currency.currejncySymbol osc
        oracle = Oracle
            { oSymbol   = cs
            , oOperator = pkh
            , oFee      = opFees op
            , oAsset    = AssetClass (opSymbol op, opToken op)
            }
    logInfo @String $ "started oracle " ++ show oracle
    return oracle

updateOracle :: forall w s. HasBlockchainActions s => Oracle -> Integer -> Contract w s Text ()
updateOracle oracle x = do
    m <- findOracle oracle
    let c = Constraints.mustPayToTheScript x $ assetClassValue (oracleAsset oracle) 1
    case m of
        -- Case where there is no initial value at the oracle address.
        Nothing -> do
            ledgerTx <- submitTxConstraints (oracleInst oracle) c
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "set initial oracle value to " ++ show x
        -- Case where there is an existing value we want to replace.
            let lookups = Constraints.unspentOutputs (Map.singleton oref o)     <>
                          Constraints.scriptInstanceLookups (oracleInst oracle) <>
                          Constraints.otherScript (oracleValidator oracle)
                          -- Constraint says to spend the outputs in the script, but also (c) pay the NFT back to the script.
                tx      = c <> Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData Update)
            -- Automatically balances the transaction, meaning any fees are sent to wallet by default, and transaction fees to pay are taken from the wallet.
            ledgerTx <- submitTxConstraintsWith @Oracling lookups tx
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "updated oracle value to " ++ show x

-- finds the oracle, returning triple containing information. Confirms the oracle exists and is set.
findOracle :: forall w s. HasBlockchainActions s => Oracle -> Contract w s Text (Maybe (TxOutRef, TxOutTx, Integer))
findOracle oracle = do
    utxos <- Map.filter f <$> utxoAt (oracleAddress oracle)
    return $ case Map.toList utxos of
        [(oref, o)] -> do
            x <- oracleValue (txOutTxOut o) $ \dh -> Map.lookup dh $ txData $ txOutTxTx o
            return (oref, o, x)
        _           -> Nothing
  where
    f :: TxOutTx -> Bool
    f o = assetClassValueOf (txOutValue $ txOutTxOut o) (oracleAsset oracle) == 1

-- Enpoint action that takes care of the above to setup the oracle (start and update)
type OracleSchema = BlockchainActions .\/ Endpoint "update" Integer

runOracle :: OracleParams -> Contract (Last Oracle) OracleSchema Text ()
runOracle op = do
    -- Start the oracle
    oracle <- startOracle op
    -- tell is needed to communicate this parameter to the outside world (so others can use it)
    -- tell outputs information from the contract 
    -- Last is monoid operation that remembers the last "Just" value.
    tell $ Last $ Just oracle
    go oracle
  where
    -- Handles looping forever, always waiting for new update calls after each one.
    go :: Oracle -> Contract (Last Oracle) OracleSchema Text a
    go oracle = do
        x <- endpoint @"update"
        updateOracle oracle x
        go oracle
