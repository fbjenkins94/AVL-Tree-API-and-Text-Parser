module CSE230.BST where

import qualified Data.Map as Map
import Test.QuickCheck 

-- ============================================================================
-- | Binary Search Trees 
-- ============================================================================

{- For this problem, you will use Haskell's data types to
   implement an _Abstract Set_ datatype that implements
   the following API:

   -- | The Set data type
   data Set a

   -- | `contains x ys` returns `True` if and only if `x` is a member of the set `ys`
   contains :: (Ord a) => a -> Set a -> Bool

   -- | `add x xs` returns the (new) set obtained by inserting `x` into the set `xs`
   add :: (Ord a) => a -> Set a -> Set a

   -- | `remove x xs` returns the (new) set obtained by deleting `x` from the set `xs`
   remove :: (Ord a) => a -> Set a -> Set a

-}

-- | The BST Data Type ------------------------------------------------------------------ 

poo :: BST Int String
poo = Bind (5) "V" (Emp) (Emp)

data BST k v 
  = Emp                          -- ^ Empty tree
  | Bind k v (BST k v) (BST k v) -- ^ Node with key=k, val=v, and left, right subtrees
  deriving (Show)

-- | `isBSO t` tests whether a tree satisfies the "binary-search-order" invariant -------
isBSO ::  Ord k => BST k v -> Bool
isBSO Emp            = True
isBSO (Bind k _ l r) = allKeys (\kl -> kl < k) l    -- all keys in `l` are less    than k
                    && allKeys (\kr -> k < kr) r    -- all keys in `r` are greater than k 
                    && isBSO l                      -- left-subtree is BS-ordered
                    && isBSO r                      -- right-subtree is BS-ordered

allKeys :: (k -> Bool) -> BST k v -> Bool
allKeys _ Emp            = True
allKeys p (Bind k _ l r) = p k && allKeys p l && allKeys p r

-- | To test your implementation, we will define a type of operations over trees.
--   This will let us randomly generate (programs) sequences of operations that 
--   manipulate the trees.

data BSTop k v 
  = BSTadd k v  -- "add key value" operation 
  | BSTdel k    -- "delete key" operation
  deriving (Eq, Show)

-- | A function that builds a tree from a list of operations

ofBSTops ::  Ord k => [BSTop k v] -> BST k v
ofBSTops ops            = foldr doOp Emp ops
  where 
      doOp (BSTadd k v) = bstInsert k v
      doOp (BSTdel k)   = bstDelete k    

-- | We can also build a "golden" or "reference" implementation using the standard 
--   libraries `Map` datatype

mapOfBSTops ::  Ord k => [BSTop k a] -> Map.Map k a
mapOfBSTops ops         = foldr doOp Map.empty ops
  where 
      doOp (BSTadd k v) = Map.insert k v
      doOp (BSTdel k)   = Map.delete k

-- | The following functions will let us generate random BST operations 

keys :: [Int]
keys = [0..10]

genBSTadd :: Gen (BSTop Int Char)
genBSTadd = do 
  k <- elements keys
  v <- elements ['a'..'z']
  return (BSTadd k v) 

genBSTdel :: Gen (BSTop Int Char)
genBSTdel = do 
  k <- elements keys 
  return (BSTdel k)

genBSTop ::  Gen (BSTop Int Char)
genBSTop  = frequency [(5, genBSTadd), (1, genBSTdel)]

---------------------------------------------------------------------------------------------------
-- | Part (a) Insertion
--   Write a function`bstInsert k v t` that inserts a key `k` with value `v` into the tree `t`. 
--   If `k` already exists in `t` then its value should be *replaced* with `v`. 
---------------------------------------------------------------------------------------------------



bstInsert :: (Ord k) => k -> v -> BST k v -> BST k v
bstInsert = (\k v avl -> case avl of 
  Emp -> Bind k v (Emp) (Emp)
  Bind a b l r -> if (a > k) 
    then do 
      let avl = Bind a b (bstInsert k v l) r
      if (isBal avl) then avl else do
        case avl of
          Emp -> Emp
          Bind z1 z2 z3 z4 -> leftBalanceAVL k avl z3 
    else (if (a < k) then do
      let avl = Bind a b l (bstInsert k v r)
      if (isBal avl) then avl else do
        case avl of
          Emp -> Emp
          Bind z1 z2 z3 z4 -> rightBalanceAVL k avl z4
      else do
        let avl = Bind a v l r
        avl))

leftBalanceAVL :: (Ord k) => k -> BST k v -> BST k v -> BST k v
leftBalanceAVL k (avl1) (avl2) = case avl2 of
  Emp -> Emp
  Bind k2 v2 l2 r2 -> if k > k2 then do
    case avl1 of
      Emp -> Emp
      Bind k1 v1 l1 r1 -> do 
        case r2 of 
          Emp -> Emp
          Bind k3 v3 l3 r3 -> do 
            let t1 = Bind k1 v1 r3 r1
            let t2 = Bind k2 v2 l2 l3
            let t3 = Bind k3 v3 t2 t1
            t3
    else do 
      case avl1 of
        Emp -> Emp
        Bind k1 v1 l1 r1 -> do  
                let t1 = Bind k1 v1 r2 r1
                let t2 = Bind k2 v2 l2 t1
                t2 


rightBalanceAVL :: (Ord k) => k -> BST k v -> BST k v -> BST k v
rightBalanceAVL k (avl1) (avl2) = case avl2 of
  Emp -> Emp
  Bind k2 v2 l2 r2 -> if k < k2 then do
    case avl1 of
      Emp -> Emp
      Bind k1 v1 l1 r1 -> do 
        case l2 of 
          Emp -> Emp
          Bind k3 v3 l3 r3 -> do 
            let t1 = Bind k1 v1 l1 l3
            let t2 = Bind k2 v2 r3 r2
            let t3 = Bind k3 v3 t1 t2
            t3
    else do 
      case avl1 of
        Emp -> Emp
        Bind k1 v1 l1 r1 -> do  
                let t1 = Bind k1 v1 l1 l2
                let t2 = Bind k2 v2 t1 r2
                t2  
  


-- When you are done, your code should satisfy the following QC properties.

prop_insert_bso :: Property
prop_insert_bso = forAll (listOf genBSTadd) $ \ops ->
                    isBSO (ofBSTops ops)


prop_insert_map = forAll (listOf genBSTadd) $ \ops -> 
                    eqMap (ofBSTops ops) (mapOfBSTops ops)

-- >>> quickCheck prop_insert_bso
-- +++ OK, passed 100 tests.
--


-- >>> quickCheck prop_insert_map
-- +++ OK, passed 100 tests.
--



---------------------------------------------------------------------------------------------------
-- | (b) Deletion
--   Write a function `bstDelete k t` that removes the key `k` from the tree `t` 
--   and leaves the other key-values unchanged. If `k` is absent from the `t`, 
--   then the tree `t` is returned unchanged as the output. 
---------------------------------------------------------------------------------------------------

bstDelete :: (Ord k) => k -> BST k v -> BST k v
bstDelete = (\k bst -> case bst of 
  Emp -> Emp
  Bind a b l r -> 
    -- if deleted value is more than current then recurse to the right
    if (a > k) 
    then do 
      let bst = Bind a b (bstDelete k l) r
      if (isBal bst) 
      then bst 
      else case bst of
        Emp -> Emp
        Bind k2 v2 l2 r2 -> 
          if height l2 > height r2
          then do
            let avl = balanceLeft bst l2
            avl
          else do 
            let avl = balanceRight bst r2  
            avl
    -- else if deleted value is less than current then then recurse to the left
    else 
      if (a < k) 
      then do
        let bst = Bind a b l (bstDelete k r)
        if (isBal bst) 
        then bst 
        else case bst of
          Emp -> Emp
          Bind k2 v2 l2 r2 -> 
            if height l2 > height r2
            then do
              let avl = balanceLeft bst l2
              avl
            else do 
              let avl = balanceRight bst r2  
              avl
      -- else if deleted value is equal to current, check how many children 
      else case l of 
        --Delete node with no children
        Emp -> case r of 
          Emp -> Emp
          -- Delete node with only right child
          Bind a2 b2 l2 r2 -> do 
            let x1 = Bind a2 b2 l2 r2
            if (isBal x1) 
            then x1 
            else case x1 of
              Emp -> Emp
              Bind k2 v2 l2 r2 -> 
                if height l2 > height r2
                then do
                  let x2 = balanceLeft x1 l2
                  x2
                else do 
                  let x2 = balanceRight x1 r2  
                  x2
        Bind a2 b2 l2 r2 -> case r of
          -- delete node with only left child
          Emp -> do 
            let x1 = Bind a2 b2 l2 r2
            if (isBal x1) 
            then x1 
            else case x1 of
              Emp -> Emp
              Bind k2 v2 l2 r2 -> 
                if height l2 > height r2
                then do
                  let x2 = balanceLeft x1 l2
                  x2
                else do 
                  let x2 = balanceRight x1 r2  
                  x2
          -- delete node with two children
          Bind a3 b3 l3 r3 -> do
            let x1 = replaceNode bst r
            if (isBal x1) 
            then x1 
            else case x1 of
              Emp -> Emp
              Bind k2 v2 l2 r2 -> 
                if height l2 > height r2
                then do
                  let x2 = balanceLeft x1 l2
                  x2
                else do 
                  let x2 = balanceRight x1 r2  
                  x2)

replaceNode :: (Ord k) => BST k v -> BST k v -> BST k v
replaceNode newBST nextBST = case nextBST of 
  Bind a b l r -> case l of
    Bind a2 b2 l2 r2 -> replaceNode newBST l
    Emp -> case newBST of 
      Bind a3 b3 l3 r3 -> do
        let temp1 = a
        let temp2 = b
        let bst2 = (avlDelete a newBST)
        case bst2 of Bind a4 b4 l4 r4 -> Bind temp1 temp2 l4 r4
                     Emp -> Emp
      Emp -> Emp 
  Emp -> Emp

avlDelete :: (Ord k) => k -> BST k v -> BST k v
avlDelete = (\k bst -> case bst of 
  Emp -> Emp
  Bind a b l r -> 
    if (a > k) 
    then do 
      let bst = Bind a b (avlDelete k l) r
      bst 
    else 
      if (a < k) 
        then do
          let bst = Bind a b l (avlDelete k r)
          bst
      else case l of 
        Emp -> (case r of 
          Emp -> Emp
          Bind a2 b2 l2 r2 -> Bind a2 b2 l2 r2)
        Bind a2 b2 l2 r2 -> (case r of
          Emp -> Bind a2 b2 l2 r2
          Bind a3 b3 l3 r3 -> replaceNode bst r))

balanceLeft avl1 avl2 = do 
  case avl2 of
    Emp -> Emp
    Bind k2 v2 l2 r2 -> 
      if height l2 > height r2 
      then case avl1 of 
        Emp -> Emp
        Bind k1 v1 l1 r1 -> do
          let t1 = Bind k1 v1 r2 r1
          let t2 = Bind k2 v2 l2 t1
          t2
      else case avl1 of 
        Emp -> Emp
        Bind k1 v1 l1 r1 -> case r2 of
          Emp -> Emp
          Bind k3 v3 l3 r3 -> do
            let t1 = Bind k1 v1 r3 r1
            let t2 = Bind k2 v2 l2 l3
            let t3 = Bind k3 v3 t2 t1
            t3
  
balanceRight avl1 avl2 = do
  case avl2 of
    Emp -> Emp
    Bind k2 v2 l2 r2 -> 
      if height l2 < height r2 
      then case avl1 of 
        Emp -> Emp
        Bind k1 v1 l1 r1 -> do
          let t1 = Bind k1 v1 l1 l2
          let t2 = Bind k2 v2 t1 r2
          t2
      else case avl1 of 
        Emp -> Emp
        Bind k1 v1 l1 r1 -> case l2 of
          Emp -> Emp
          Bind k3 v3 l3 r3 -> do 
            let t1 = Bind k1 v1 l1 l3
            let t2 = Bind k2 v2 r3 r2
            let t3 = Bind k3 v3 t1 t2
            t3




-- When you are done, your code should satisfy the following QC properties.

prop_delete_bso :: Property
prop_delete_bso = forAll (listOf genBSTop) $ \ops ->
                    isBSO (ofBSTops ops)

prop_delete_map = forAll (listOf genBSTop) $ \ops ->
                    eqMap (ofBSTops ops) (mapOfBSTops ops)

eqMap :: (Ord k, Eq v) => BST k v -> Map.Map k v -> Bool
eqMap bst map = toBinds bst == Map.toAscList map
   where
    toBinds ::  BST k v -> [(k, v)]
    toBinds Emp            = []
    toBinds (Bind k v l r) = toBinds l ++ [(k,v)] ++ toBinds r


-- >>> quickCheck prop_delete_bso
-- +++ OK, passed 100 tests.
--

-- >>> quickCheck prop_delete_map
-- +++ OK, passed 100 tests.
--



---------------------------------------------------------------------------------------------------
-- | (c) Balanced Trees [These are "AVL Trees" where the height difference between left/right <= 2]
---------------------------------------------------------------------------------------------------

-- | `height t` evaluates to the "height" of the BST `t` 
height :: BST k v -> Int
height (Bind _ _ l r) = 1 + max (height l) (height r)
height Emp            = 0

-- | `isBal t` returns `True` if the tree `t` is *balanced*
isBal :: BST k v -> Bool
isBal (Bind _ _ l r) = isBal l && isBal r && abs (height l - height r) <= 2
isBal Emp            = True

-- | Write a balanced tree generator
genBal :: Gen (BST Int Char)
genBal = do
  k <- elements keys
  v <- elements ['a'..'z']
  c1 <- elements keys
  c2 <- elements keys
  let c = c1*c2
  let a = bstInsert k v Emp
  let a2 = buildAVL k v a c
  a2
    where
      buildAVL k v avl count  = do
        a <- elements keys
        b <- elements ['a'..'z']
        let avl2 = bstInsert a b avl
        let count2 = count - 1
        if count2 <= 0 
        then return avl2
        else do 
          let avl3 = buildAVL k v avl2 count2
          avl3



-- such that
prop_genBal :: Property
prop_genBal = forAll genBal isBal

-- >>> quickCheck prop_genBal
-- +++ OK, passed 100 tests.
--


---------------------------------------------------------------------------------------------------
-- | (d) Height Balancing (** HARD: EXTRA CREDIT see [NOTE:Balancing] below  **) 
---------------------------------------------------------------------------------------------------
-- | Modify your `insert` and `delete` functions so that 
--   if given balanced trees as input, they return balanced trees as output.
--   That is, they satisfy the properties
---------------------------------------------------------------------------------------------------
--


prop_insert_bal :: Property
prop_insert_bal = forAll (listOf genBSTadd) (\ops -> isBal (ofBSTops ops))

prop_delete_bal ::  Property
prop_delete_bal = forAll (listOf genBSTop) (\ops -> isBal (ofBSTops ops))

-- >>> quickCheck prop_insert_bal
-- +++ OK, passed 100 tests.
--


-- >>> quickCheck prop_delete_bal 
-- +++ OK, passed 100 tests.
--

---------------------------------------------------------------------------------------------------
-- | [NOTE:Balancing] One "trivial" way to achieve this is to 
--   (1) convert the BST to a list of key-value pairs 
--   (2) perform the insertion or deletion on the list 
--   (3) convert the list back into a BST
--
--   However, this defeats the purpose of balancing which is to make `insert` and `delete` efficient
--   O(log n) operations instead of O(n). 
-- 
--   DO NOT CONVERT YOUR BST TO A LIST or similar or you WILL GET 0 for the assignment!
---------------------------------------------------------------------------------------------------




