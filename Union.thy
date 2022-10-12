theory Union
  imports Main "HOL-Library.Multiset"
begin

fun f :: "nat \<Rightarrow> nat set" where
"f 0 = {}" |
"f (Suc n) = {n} \<union> f n"

value [simp] "\<Union>i. f i" (* without [simp], code generator will error *)
value "\<Union>i::nat<m. f i"
value "\<Union>i::nat<10. f i"

datatype mynat = Z | S mynat

fun g :: "nat \<Rightarrow> mynat" where
"g 0 = Z" |
"g (Suc n) = S (g n)"

value [simp] "\<Union>i. {g i}"
value "\<Union>i<m. {g i}"
value "\<Union>i<10. {g i}"

fun h :: "nat \<Rightarrow> mynat" where
"h n = (if n mod 5 = 0 then Z else 
  case n of 
    0 \<Rightarrow> Z |
    (Suc m) \<Rightarrow> S (h m))"

value [simp] "\<Union>i. {h i}"
value "\<Union>i<m. {h i}"
value "\<Union>i<10. {h i}"

fun l :: "nat \<Rightarrow> mynat multiset" where
"l 0 = {#}" |
"l (Suc n) = add_mset (h (Suc n)) (l n)"

value "l 10"

end