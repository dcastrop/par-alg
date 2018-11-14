module Fun2Atoms where


split :: [Int] -> Either (Either () Int) ([Int], [Int])
split [] = Left (Left ())
split [x] = Left (Right x)
split l   = Right $ go l [] []
  where
    go [] l r = (l, r)
    go (x:xs) l r = go xs r (x : l)

merge :: Either (Either () Int) ([Int], [Int]) -> [Int]
merge (Left (Left _)) = []
merge (Left (Right x)) = [x]
merge (Right (l, r)) = go l r
  where
    go l1@(h1 : t1) l2@(h2 : t2)
      | h1 <= h2 = h1 : go t1 l2
      | otherwise = h2 : go l1 t2
    go l1 l2 = l1 ++ l2

