%default total

-- replace : (x = y) -> P x -> P y
disjoint : (n : Nat) -> Z = S n -> Void
disjoint n prf = replace {P = disjointTy} prf () where
  disjointTy : Nat -> Type
  disjointTy Z = ()
  disjointTy (S k) = Void

-- empty1 : Void
-- empty1 = hd [] where
--   hd : List a -> a
--   hd (x :: xs) = x

-- empty2 : Void
-- empty2 = empty2
