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

module Week07.EvenOdd
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , endpoints
    ) where

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (FromJSON, ToJSON)
import qualified Data.Map             as Map
import           Data.Text            (Text)
import           GHC.Generics         (Generic)
import           Plutus.Contract      as Contract hiding (when)
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Ledger.Value
import           Playground.Contract  (ToSchema)
import           Prelude              (Semigroup (..))
import qualified Prelude

data Game = Game
    -- First and second players
    { gFirst          :: !PubKeyHash
    , gSecond         :: !PubKeyHash
    -- Denotes the amount of lovelace at stake in the game
    , gStake          :: !Integer
    -- Time by which 2nd player has to make a room before stake can be reclaimed
    , gPlayDeadline   :: !Slot
    -- Time by which 1st player has to prove they have won the game.
    , gRevealDeadline :: !Slot
    -- Arbitrary NFT to identify correct instance of UTXO being used. (similar to oracle)
    -- Using the Datum of a UTXO sitting at address of this contract to keep track of where we are in the game.
    , gToken          :: !AssetClass
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Game

-- The two moves the players can make.
data GameChoice = Zero | One
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

-- Define Eq for it to work in Plutus Script
instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Zero == Zero = True
    One  == One  = True
    _    == _    = False

PlutusTx.unstableMakeIsData ''GameChoice

-- Used as state. BysteString is the hash submitted by the 1st player, Maybe GameChoise is 2nd player.
-- It's a Maybe because the GameChoisce is made later after the 1st player engages.
data GameDatum = GameDatum ByteString (Maybe GameChoice)
    deriving Show

-- Define Eq for GameDatum
instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')

PlutusTx.unstableMakeIsData ''GameDatum

-- Play is the 2nd player option to play. Reveal is the nonce. 
-- ClaimFirst to reclaim. ClaimSecond to claim win.
data GameRedeemer = Play GameChoice | Reveal ByteString | ClaimFirst | ClaimSecond
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromData d

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsZero' bsOne' dat red ctx =
    traceIfFalse "token missing from input" (assetClassValueOf (txOutValue ownInput) (gToken game) == 1) &&
    case (dat, red) of
        -- Pertains to 2nd player's move
        (GameDatum bs Nothing, Play c) ->
            -- Ensure 2nd player made the move.
            traceIfFalse "not signed by second player"   (txSignedBy info (gSecond game))                                   &&
            -- Ensure 1st player has put up stake (existing stake)
            traceIfFalse "first player's stake missing"  (lovelaces (txOutValue ownInput) == gStake game)                   &&
            -- Ensure 2nd player has put up stake (adding their own stake)
            traceIfFalse "second player's stake missing" (lovelaces (txOutValue ownOutput) == (2 * gStake game))            &&
            -- Ensure output Datum is correct
            traceIfFalse "wrong output datum"            (outputDatum == GameDatum bs (Just c))                             &&
            -- Ensure move is being made before the deadline
            traceIfFalse "missed deadline"               (to (gPlayDeadline game) `contains` txInfoValidRange info)         &&
            -- Ensure the NFT is moving to the output.
            traceIfFalse "token missing from output"     (assetClassValueOf (txOutValue ownOutput) (gToken game) == 1)

        -- Pertains to player 1 winning.
        (GameDatum bs (Just c), Reveal nonce) ->
            -- Ensure 1st player made the move.
            traceIfFalse "not signed by first player"    (txSignedBy info (gFirst game))                                    &&
            -- Confirm the nonce matches (hashes correctly)
            traceIfFalse "commit mismatch"               (checkNonce bs nonce c)                                            &&
            -- Done before deadline
            traceIfFalse "missed deadline"               (to (gRevealDeadline game) `contains` txInfoValidRange info)       &&
            -- Input has stake of both players.
            traceIfFalse "wrong stake"                   (lovelaces (txOutValue ownInput) == (2 * gStake game))             &&
            -- NFT back to first player 
            traceIfFalse "NFT must go to first player"   nftToFirst

        -- 1st player wants stake back (deadline passed, 2nd player did not engage)
        (GameDatum _ Nothing, ClaimFirst) ->
            -- Signed by 1st player
            traceIfFalse "not signed by first player"    (txSignedBy info (gFirst game))                                    &&
            -- Deadline has passed
            traceIfFalse "too early"                     (from (1 + gPlayDeadline game) `contains` txInfoValidRange info)   &&
            -- Stake provided by 1st player
            traceIfFalse "first player's stake missing"  (lovelaces (txOutValue ownInput) == gStake game)                   &&
            -- NFT back to first player 
            traceIfFalse "NFT must go to first player"   nftToFirst

        -- 2nd player has won
        (GameDatum _ (Just _), ClaimSecond) ->
            -- Signed by 2nd player
            traceIfFalse "not signed by second player"   (txSignedBy info (gSecond game))                                   &&
            -- After the reveal deadline has passed
            traceIfFalse "too early"                     (from (1 + gRevealDeadline game) `contains` txInfoValidRange info) &&
            -- Ensures correct stakes available
            traceIfFalse "wrong stake"                   (lovelaces (txOutValue ownInput) == (2 * gStake game))             &&
            -- NFT back to first player 
            traceIfFalse "NFT must go to first player"   nftToFirst

        -- Fail validation on all other cases
        _                              -> False
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxOut
    ownInput = case findOwnInput ctx of
        Nothing -> traceError "game input missing"
        Just i  -> txInInfoResolved i

    ownOutput :: TxOut
    ownOutput = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one game output"

    -- Given exactly 1 output to the script, will return the Datum
    outputDatum :: GameDatum
    outputDatum = case gameDatum ownOutput (`findDatum` info) of
        Nothing -> traceError "game output datum not found"
        Just d  -> d

    -- Used for first player to prove they have won
    checkNonce :: ByteString -> ByteString -> GameChoice -> Bool
    checkNonce bs nonce cSecond = sha2_256 (nonce `concatenate` cFirst) == bs
      where
        cFirst :: ByteString
        cFirst = case cSecond of
            Zero -> bsZero'
            One  -> bsOne'

    -- Puts the UTXO NFT back to the first player to reset the game.
    nftToFirst :: Bool
    nftToFirst = assetClassValueOf (valuePaidTo info $ gFirst game) (gToken game) == 1

data Gaming
instance Scripts.ScriptType Gaming where
    type instance DatumType Gaming = GameDatum
    type instance RedeemerType Gaming = GameRedeemer

bsZero, bsOne :: ByteString
bsZero = "0"
bsOne  = "1"

-- Game only argument, the bytestrings are constant
gameInst :: Game -> Scripts.ScriptInstance Gaming
gameInst game = Scripts.validator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsZero
        `PlutusTx.applyCode` PlutusTx.liftCode bsOne)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

-- Boilerplate validator and address
gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . gameInst

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

-- Offchain code.
-- Helper function that gets the game and tries to find the UTXO
findGameOutput :: HasBlockchainActions s => Game -> Contract w s Text (Maybe (TxOutRef, TxOutTx, GameDatum))
findGameOutput game = do
    -- All utxo at the game address
    utxos <- utxoAt $ gameAddress game
    return $ do
        -- Use the find function to check if output contains our token (NFT)
        (oref, o) <- find f $ Map.toList utxos
        -- Get the datum from the UTXO
        dat       <- gameDatum (txOutTxOut o) (`Map.lookup` txData (txOutTxTx o))
        -- Return the triple
        return (oref, o, dat)
  where
    f :: (TxOutRef, TxOutTx) -> Bool
    f (_, o) = assetClassValueOf (txOutValue $ txOutTxOut o) (gToken game) == 1

-- Contracts for both players to play the game.
-- First player. (owner of the wallet that invokes this contract)
data FirstParams = FirstParams
    { fpSecond         :: !PubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !Slot
    , fpRevealDeadline :: !Slot
    -- Nonce used to conceal choice.
    , fpNonce          :: !ByteString
    -- Currency and tokenName for the NFT
    , fpCurrency       :: !CurrencySymbol
    , fpTokenName      :: !TokenName
    -- Choice made.
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

firstGame :: forall w s. HasBlockchainActions s => FirstParams -> Contract w s Text ()
firstGame fp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = AssetClass (fpCurrency fp, fpTokenName fp)
            }
        -- Stake and the NFT Token
        v    = lovelaceValueOf (fpStake fp) <> assetClassValue (gToken game) 1
        -- Choice
        c    = fpChoice fp
        -- Hashed result of choice
        bs   = sha2_256 $ fpNonce fp `concatenate` if c == Zero then bsZero else bsOne
        -- Constraints produce a script output at the script address, Datuim and Value computed.
        tx   = Constraints.mustPayToTheScript (GameDatum bs Nothing) v
    ledgerTx <- submitTxConstraints (gameInst game) tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "made first move: " ++ show (fpChoice fp)

    -- Wait until after the deadline
    void $ awaitSlot $ 1 + fpPlayDeadline fp

    -- Check result.
    m <- findGameOutput game
    case m of
        Nothing             -> throwError "game output not found"
        Just (oref, o, dat) -> case dat of
            -- Option if player 2 did not play.
            GameDatum _ Nothing -> do
                logInfo @String "second player did not play"
                let lookups = Constraints.unspentOutputs (Map.singleton oref o) <>
                              Constraints.otherScript (gameValidator game)
                              -- ClaimFirst to get stake back
                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData ClaimFirst)
                ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'
                void $ awaitTxConfirmed $ txId ledgerTx'
                logInfo @String "reclaimed stake"

            -- Option if player 2 made a move.
            GameDatum _ (Just c') | c' == c -> do
                logInfo @String "second player played and lost"
                let lookups = Constraints.unspentOutputs (Map.singleton oref o)                                         <>
                              Constraints.otherScript (gameValidator game)
                              -- Reveal nonce to prove won.
                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Reveal $ fpNonce fp) <>
                              Constraints.mustValidateIn (to $ fpRevealDeadline fp)
                ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'
                void $ awaitTxConfirmed $ txId ledgerTx'
                logInfo @String "victory"

            _ -> logInfo @String "second player played and won"

-- Second player.
data SecondParams = SecondParamsj
    { spFirst          :: !PubKeyHash
    -- Stake
    , spStake          :: !Integer
    -- Deadlines
    , spPlayDeadline   :: !Slot
    , spRevealDeadline :: !Slot
    -- Currency (NFT)
    , spCurrency       :: !CurrencySymbol
    , spTokenName      :: !TokenName
    -- Choice
    , spChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

secondGame :: forall w s. HasBlockchainActions s => SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = AssetClass (spCurrency sp, spTokenName sp)
            }
    m <- findGameOutput game
    case m of
        -- Game found, make a move
        Just (oref, o, GameDatum bs Nothing) -> do
            logInfo @String "running game found"
            let token   = assetClassValue (gToken game) 1
            let v       = let x = lovelaceValueOf (spStake sp) in x <> x <> token
                c       = spChoice sp
                lookups = Constraints.unspentOutputs (Map.singleton oref o)                            <>
                          Constraints.otherScript (gameValidator game)                                 <>
                          Constraints.scriptInstanceLookups (gameInst game)
                tx      = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Play c) <>
                          Constraints.mustPayToTheScript (GameDatum bs $ Just c) v                     <>
                          Constraints.mustValidateIn (to $ spPlayDeadline sp)
            ledgerTx <- submitTxConstraintsWith @Gaming lookups tx
            let tid = txId ledgerTx
            void $ awaitTxConfirmed tid
            logInfo @String $ "made second move: " ++ show (spChoice sp)

            -- Wait for the 1st player to reveal
            void $ awaitSlot $ 1 + spRevealDeadline sp

            m' <- findGameOutput game
            case m' of
                -- Player 1 has won
                Nothing             -> logInfo @String "first player won"
                -- Player 1 did not reveal or did and lost.
                Just (oref', o', _) -> do
                    logInfo @String "first player didn't reveal"
                    let lookups' = Constraints.unspentOutputs (Map.singleton oref' o')                              <>
                                   Constraints.otherScript (gameValidator game)
                        tx'      = Constraints.mustSpendScriptOutput oref' (Redeemer $ PlutusTx.toData ClaimSecond) <>
                                   Constraints.mustValidateIn (from $ 1 + spRevealDeadline sp)                      <>
                                   Constraints.mustPayToPubKey (spFirst sp) token
                    ledgerTx' <- submitTxConstraintsWith @Gaming lookups' tx'
                    void $ awaitTxConfirmed $ txId ledgerTx'
                    logInfo @String "second player won"

        -- No game found
        _ -> logInfo @String "no running game found"

type GameSchema = BlockchainActions .\/ Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract () GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    -- Bind endpoints to the contracts defined.
    first  = endpoint @"first"  >>= firstGame
    second = endpoint @"second" >>= secondGame
