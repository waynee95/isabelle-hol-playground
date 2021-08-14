theory BF_Interp
  imports Main "HOL-ex.Code_Lazy_Demo"
begin

(* Reference: https://youtu.be/bIGDIrWt5e0 *)
section \<open>Syntax\<close>

datatype bf = Inc | Dec | Out | Left | Right | Loop "bf list"

section \<open>Semantics\<close>

codatatype stream = Stream (head: int) (tail: stream) (infixr "#@" 65)

term "1 #@ 2 #@ 3 #@ xs"

code_lazy_type stream

primcorec zeros where
  "zeros = 0 #@ zeros"

value "head (tail zeros)"

record state = 
  tape_curr :: int
  tape_left :: stream
  tape_right :: stream
  out :: "int list"

fun step :: "bf list \<Rightarrow> state \<Rightarrow> bf list \<times> state" where
"step [] st = ([], st)" |
"step (Inc # cs) st = (cs, st\<lparr>tape_curr := tape_curr st + 1\<rparr>)" |
"step (Dec # cs) st = (cs, st\<lparr>tape_curr := tape_curr st - 1\<rparr>)" |
"step (Left # cs) st = (cs, st\<lparr>tape_curr := head (tape_left st),
                               tape_left := tail (tape_left st),
                               tape_right := tape_curr st #@ tape_right st
                          \<rparr>)" |
"step (Right # cs) st = (cs, st\<lparr>tape_curr := head (tape_right st),
                               tape_right := tail (tape_right st),
                               tape_left := tape_curr st #@ tape_left st
                          \<rparr>)" |
"step (Out # cs) st = (cs, st\<lparr>out := tape_curr st # out st\<rparr>)" |
"step (Loop ds # cs) st = (if tape_curr st = 0 then (cs, st) else (ds @ Loop ds # cs, st))"

definition run :: "bf list \<Rightarrow> int list option" where
"run cs = undefined"

end