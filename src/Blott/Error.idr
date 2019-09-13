module Check

import Domain as D
import Syntax as Syn

%access public export
%default total

data Error = CannotSynthTerm T
           | UsingLockedVariable
           | TypeMismatch DT DT
           | ExpectingUniverse DT
           | NbeError String
           | Misc String

Show Error where
  show (CannotSynthTerm t)   = "Cannot synthesize the type of: " ++ show t 
  show  UsingLockedVariable  = "Cannot use a variable behind a lock."
  show (TypeMismatch t1 t2)  = "Cannot equate " ++ show t1 ++ " with " ++ show t2 
  show (ExpectingUniverse d) = "Expected some universe but found " ++ show d
  show (NbeError s)          = "Normalization failure: " ++ s
  show (Misc s)              = s