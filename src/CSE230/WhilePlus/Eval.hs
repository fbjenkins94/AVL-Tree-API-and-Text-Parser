{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE ConstraintKinds           #-}

module CSE230.WhilePlus.Eval where

import qualified Data.Map as Map
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Identity
import           CSE230.WhilePlus.Types

----------------------------------------------------------------------------------------------
-- | A Combined monad that is BOTH 
--    (i) a WState-Transformer monad 
--    (ii) an Exception monad with exceptions of type Value 
----------------------------------------------------------------------------------------------
type MonadWhile m = (MonadState WState m, MonadError Value m)

----------------------------------------------------------------------------------------------
-- | `readVar x` returns the value of the variable `x` in the "current store"
----------------------------------------------------------------------------------------------
readVar :: (MonadWhile m) => Variable -> m Value
readVar x = do 
  WS s _ <- get 
  case Map.lookup x s of
    Just v  -> return v
    Nothing -> throwError (IntVal 0)

----------------------------------------------------------------------------------------------
-- | `writeVar x v` updates the value of `x` in the store to `v`
----------------------------------------------------------------------------------------------
writeVar :: (MonadState WState m) => Variable -> Value -> m ()
writeVar x v = do 
  WS s log <- get 
  let s' = Map.insert x v s
  put (WS s' log)

----------------------------------------------------------------------------------------------
-- | `printString msg` adds the message `msg` to the output log
----------------------------------------------------------------------------------------------
printString :: (MonadState WState m) => String -> m ()
printString msg = do
  WS s log <- get
  put (WS s (msg:log))


-- NOTE: See how the types of `writeVar` and `printString` say they CANNOT throw an exception!

----------------------------------------------------------------------------------------------
-- | Requirements & Expected Behavior of New Constructs
----------------------------------------------------------------------------------------------

{-
  * `Print s e` should print out (eg to stdout) log the string corresponding
     to the string `s` followed by whatever `e` evaluates to, followed by a
     newline --- for example, `Print "Three: " (IntVal 3)' should "display" 
     i.e. add to the output log, the String  
     
     "Three: IntVal 3\n",

  * `Throw e` evaluates the expression `e` and throws it as an exception, and

  * `Try s x h` executes the statement `s` and if in the course of
     execution, an exception is thrown, then the exception comes shooting
     up and is assigned to the variable `x` after which the *handler*
     statement `h` is executed.

  In the case of exceptional termination, 

  * the output `wStore` should be the state *at the point where the last exception was thrown, and 

  * the output `wLog` should include all the messages *upto* that point
   
  * Reading an undefined variable should raise an exception carrying the value `IntVal 0`.

  * Division by zero should raise an exception carrying the value `IntVal 1`.

  * A run-time type error (addition of an integer to a boolean, comparison of
    two values of different types) should raise an exception carrying the value
    `IntVal 2`.
-}


------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------

evalE :: (MonadWhile m) => Expression -> m Value
evalE (Var x)      = readVar x
evalE (Val v)      = return v
evalE (Op o e1 e2) = do
  n1 <- evalE e1 `catchError` (\err -> throwError err)
  n2 <- evalE e2 `catchError` (\err -> throwError err)
  semantics o n1 n2

semantics :: (MonadWhile m) => Bop -> Value -> Value -> m Value
semantics Plus (IntVal a) (IntVal b)                    = return (intOp  (+) (IntVal a) (IntVal b))
semantics Plus _ _                                      = throwError (IntVal 2)
semantics Minus (IntVal a) (IntVal b)                   = return (intOp (-) (IntVal a) (IntVal b))
semantics Minus _ _                                     = throwError (IntVal 2)
semantics Times (IntVal a) (IntVal b)                   = return (intOp  (*) (IntVal a) (IntVal b))
semantics Times _ _                                     = throwError (IntVal 2)
semantics Divide (IntVal a) (IntVal b)                  = if b == 0
                                                          then throwError (IntVal 1)
                                                          else return (intOp  (div) (IntVal a) (IntVal b))
semantics Divide _ _                                    = throwError (IntVal 2)
semantics Gt (IntVal a) (IntVal b)                    = return (boolOp (>) (IntVal a) (IntVal b))
semantics Gt _ _                                        = throwError (IntVal 2)
semantics Ge (IntVal a) (IntVal b)                    = return (boolOp (>=) (IntVal a) (IntVal b))
semantics Ge _ _                                        = throwError (IntVal 2)
semantics Lt (IntVal a) (IntVal b)                    = return (boolOp (<) (IntVal a) (IntVal b))
semantics Lt _ _                                        = throwError (IntVal 2)
semantics Le (IntVal a) (IntVal b)                    = return (boolOp (<=) (IntVal a) (IntVal b))
semantics Le _ _                                        = throwError (IntVal 2)


intOp :: (Int -> Int -> Int) -> Value -> Value -> Value
intOp op (IntVal x) (IntVal y)  = IntVal (x `op` y)
intOp _  _            _             = IntVal 0

boolOp :: (Int -> Int -> Bool) -> Value -> Value -> Value
boolOp op (IntVal x) (IntVal y) = BoolVal (x `op` y)
boolOp _  _            _            = BoolVal False

------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------
------------------------------------------------------------


evalS :: (MonadWhile m) => Statement -> m ()
evalS w@(While e s)    = do 
  a <- evalE e `catchError` (\err -> throwError err) 
  case a of
    BoolVal b -> if b then do { 
      evalS s `catchError` (\err -> throwError err) ; 
      evalS w `catchError` (\err -> throwError err) } `catchError` (\err -> throwError err)
      else evalS Skip 
    _ -> throwError (IntVal 2) 

evalS Skip             = do
  a <- get
  put a

evalS (Sequence s1 s2) = do
  evalS s1 `catchError` (\err -> throwError err)
  evalS s2 `catchError` (\err -> throwError err)

evalS (Assign x e )    = do 
  a <- evalE e `catchError` (\err -> throwError err)
  writeVar x a  

evalS (If e s1 s2)     = do 
  a <- evalE e `catchError` (\err -> throwError err) 
  case a of
    BoolVal b -> if b then do evalS s1 else evalS s2 
    IntVal b -> throwError (IntVal 2) 

evalS (Print s e )     = do
  a <- evalE e `catchError` (\err -> throwError err)
  let b = show a 
  let s2 = s ++ b
  printString s2

evalS (Throw e)         = do
  a <- evalE e `catchError` (\err -> throwError err)
  throwError a

evalS (Try s1 v s2)     = do
  evalS s1 `catchError` (\err -> do 
    case err of 
      (IntVal x) -> do 
        a <- evalE (Val (IntVal x))
        evalS (Assign v (Val a))
        evalS s2
      (BoolVal x) -> do
        a <- evalE (Val (BoolVal x))
        evalS (Assign v (Val a))
        evalS s2 
      _ -> evalS s2)


               

--------------------------------------------------------------------------
-- | Next, we will implement a *concrete instance* of a monad `m` that
--   satisfies the constraints of MonadWhile:
--------------------------------------------------------------------------

type Eval a = ExceptT Value (StateT WState (Identity)) a

--------------------------------------------------------------------------
-- | `runEval` implements a function to *run* the `Eval a` action from 
--   a starting `WState`. You can read the docs for `runState` and `runExceptT` 
--------------------------------------------------------------------------
runEval :: Eval a -> WState -> (Either Value a, WState)
runEval act s = runState (runExceptT act) s




{- | `execute sto stmt` returns a triple `(sto', exn, log)` where
      * `st'` is the output state,
      * `exn` is (Just v) if the program terminates with an "uncaught" exception with Value v 
         or Nothing if the program terminates without an exception.
      * `log` is the log of messages generated by the `Print` statements.

-}
execute :: Store -> Statement -> (Store, Maybe Value, String)
execute sto stmt     = (sto', leftMaybe v, unlines (reverse log))
  where
    (v, WS sto' log) = runEval (evalS stmt) (WS sto [])

leftMaybe :: Either a b -> Maybe a
leftMaybe (Left v)  = Just v
leftMaybe (Right _) = Nothing

------------------------------------------------------------------------------------
-- | When you are done you should see the following behavior 
------------------------------------------------------------------------------------

-- >>> execute initStore test1 == out1
-- True
--

-- >>> execute initStore test2 == out2
-- True
--


-- >>> execute initStore test3 == out3 