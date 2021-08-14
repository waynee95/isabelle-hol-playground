theory ArithVeri
  imports Main
begin

datatype Arith = Num nat
  | Plus Arith Arith
  | Minus Arith Arith
  | Times Arith Arith

datatype StackOp = SNum nat
  | SPlus
  | SMinus
  | STimes

fun eval :: "nat list \<Rightarrow> StackOp list \<Rightarrow> nat" where
"eval (n # _) [] = n" |
"eval ns (SNum n # xs) = eval (n # ns) xs" |
"eval (n1 # n2 # ns) (SPlus # xs) = eval ((n1+n2) # ns) xs" |
"eval (n1 # n2 # ns) (SMinus # xs) = eval ((n1-n2) # ns) xs" |
"eval (n1 # n2 # ns) (STimes # xs) = eval ((n1*n2) # ns) xs"

value "eval [] [SNum 1, SNum 2, SNum 4, STimes, SPlus]"

fun compile :: "Arith \<Rightarrow> StackOp list" where
"compile (Num n) = [SNum n]" |
"compile (Plus a1 a2) = compile a2 @ compile a1 @ [SPlus]" |
"compile (Minus a1 a2) = compile a2 @ compile a1 @ [SMinus]" |
"compile (Times a1 a2) = compile a2 @ compile a1 @ [STimes]"

value "compile (Plus (Num 1) (Times (Num 2) (Num 4)))"

fun eval' :: "Arith \<Rightarrow> nat" where
"eval' (Num n) = n" |
"eval' (Plus a1 a2) = (eval' a1) + (eval' a2)" |
"eval' (Minus a1 a2) = (eval' a1) - (eval' a2)" |
"eval' (Times a1 a2) = (eval' a1) * (eval' a2)"

value "eval' (Plus (Num 1) (Times (Num 2) (Num 4)))"

theorem compiler_correctness: "eval [] (compile a) = (eval' a)"
  sorry

end
