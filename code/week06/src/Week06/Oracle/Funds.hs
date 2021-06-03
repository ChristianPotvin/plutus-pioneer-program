-- Example 3
-- (Looks at own funds information)

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

module Week06.Oracle.Funds
    ( ownFunds
    , ownFunds'
    ) where

import           Control.Monad    hiding (fmap)
import qualified Data.Map         as Map
import           Data.Monoid      (Last (..))
import           Data.Text        (Text)
import           Plutus.Contract  as Contract hiding (when)
import           PlutusTx.Prelude hiding ((<$>))
import           Prelude          ((<$>))
import           Ledger           hiding (singleton)
import           Ledger.Value     as Value


ownFunds :: HasBlockchainActions s => Contract w s Text Value
ownFunds = do
    -- Looks up own public key
    pk    <- ownPubKey
    -- Looks up utxo at own public key
    utxos <- utxoAt $ pubKeyAddress pk
    -- Sum of all values of utxos owned.
    let v = mconcat $ Map.elems $ txOutValue . txOutTxOut <$> utxos
    -- Logs and returns
    logInfo @String $ "own funds: " ++ show (Value.flattenValue v)
    return v

-- variant of above, but then outputs via tell.
-- Runs forever, and outputs to the log each slot.
ownFunds' :: Contract (Last Value) BlockchainActions Text ()
ownFunds' = do
    handleError logError $ ownFunds >>= tell . Last . Just
    void $ Contract.waitNSlots 1
    ownFunds'
