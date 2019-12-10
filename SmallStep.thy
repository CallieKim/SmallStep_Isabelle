theory SmallStep imports Main
begin

(*Toy language*)
datatype tm = C nat | P tm tm (*Constant | Plus*)

term C (*nat \<Rightarrow> tm*)
term P (*tm \<Rightarrow> tm \<Rightarrow> tm*)

(*standard evaluator written in big step style*)
(*recursive function*)
primrec evalF :: "tm \<Rightarrow> nat" where
"evalF (C n) = n" |
"evalF (P a1 a2) = evalF a1 + evalF a2"

term evalF (*tm \<Rightarrow> nat*)

value "evalF (C 5)" (*5 :: nat*)

(*formulated as an inductively defined relation*)
inductive eval :: "tm \<Rightarrow> nat \<Rightarrow> bool"
  where
  E_Const : "eval (C n) n" |
  E_Plus : "eval t1 n1 \<Longrightarrow> eval t2 n2 \<Longrightarrow> eval (P t1 t2) (n1 + n2)"

(* commented out because of crashing with modified step definition (with value)
inductive 
  step :: "tm \<Rightarrow> tm \<Rightarrow> bool" (infix "\<longrightarrow>" 40)
  where
  ST_PlusConstConst : "P (C n1) (C n2) \<longrightarrow> C (n1 + n2)" |
  ST_Plus1 : "t1 \<longrightarrow> t1' \<Longrightarrow> P t1 t2 \<longrightarrow> P t1' t2" |
  ST_Plus2 : "t2 \<longrightarrow> t2' \<Longrightarrow> P (C n1) t2 \<longrightarrow> P (C n1) t2'"
*)

term step (*tm \<Rightarrow> tm \<Rightarrow> bool*)

(*relation r*)
consts r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

(*introducing value*)
inductive 
  vvalue :: "tm \<Rightarrow> bool"
  where
  v_const : "vvalue (C n)" 

(* step definition using value *)
inductive
  step :: "tm \<Rightarrow> tm \<Rightarrow> bool" (infix "\<longrightarrow>" 40)
  where
  ST_PlusConstConst :  "P (C n1) (C n2) \<longrightarrow> C (n1 + n2)" |
  ST_Plus1 : "t1 \<longrightarrow> t1'\<Longrightarrow> P t1 t2 \<longrightarrow> P t1' t2" |
  ST_Plus2 : "vvalue v1 \<Longrightarrow> t2 \<longrightarrow> t2' \<Longrightarrow> P v1 t2 \<longrightarrow> P v1 t2'"

lemma Example1 [simp]: "P (P (C 0) (C 3)) (P (C 2) (C 4)) \<longrightarrow> P (C (0 + 3)) (P (C 2) (C 4))"
  apply(rule ST_Plus1)
  apply(rule ST_PlusConstConst)
  done

lemma Example2 [simp] : " P (C 0) (P(C 2) (P (C 0) (C 3))) \<longrightarrow> P(C 0)(P(C 2)(C (0 + 3)))"
  apply(rule ST_Plus2)
   apply(rule v_const)
  apply(rule ST_Plus2)
   apply(rule v_const)
  apply(rule ST_PlusConstConst)
  done

declare step.intros[simp,intro]

(*to use inversion*)
inductive_cases PlusConst[elim!]: "P (C n1) (C n2) \<longrightarrow> t"
thm PlusConst
inductive_cases Plus1[elim!]: "P t1 t2 \<longrightarrow> t"
thm Plus1
inductive_cases Plus2[elim!]: "P v1 t2 \<longrightarrow> t"
thm Plus2

lemma deterministics:  "step x y1 \<Longrightarrow> step x y2 \<Longrightarrow> y2 = y1"
proof(induction  arbitrary: y2 rule: step.induct)
  case (ST_PlusConstConst n1 n2)
  from ST_PlusConstConst.prems have "y2 = C (n1 + n2)"
  proof cases
    case ST_PlusConstConst
    then show ?thesis .
  next
    case (ST_Plus1)
    from ST_Plus1(2) have False by cases
    then show ?thesis ..
  next
    case (ST_Plus2)
    from ST_Plus2(3) have False by cases
    then show ?thesis .. 
  qed
  oops


lemma strong_progress : "(vvalue t) \<or> (\<exists>t'. step t t')"
  apply(induction t)
   apply (rule disjE)
   apply (rule disjI1)
     apply(rule v_const)
    apply auto
  oops

(**)
inductive
  multi :: "(tm \<Rightarrow> tm \<Rightarrow> bool) \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> bool" (infix "\<longrightarrow>*" 40)
for R where
multi_refl:  "multi R x x" |
multi_step:  "R x y \<Longrightarrow> multi R y z \<Longrightarrow> multi R x z"


lemma multi_trans:
  "multi r x y \<Longrightarrow> multi r y z \<Longrightarrow> multi r x z"
proof(induction rule: multi.induct)
  case multi_refl thus ?case .
next
  case multi_step thus ?case by (metis multi.multi_step)
qed


lemma multi_R[simp, intro]: "R x y \<Longrightarrow> multi R x y"
  apply(rule multi_step)
   apply auto
  apply(rule multi_refl)
  done

(* 
lemma multistep_congr_1 :"multi t1 t1' \<Longrightarrow> multi (P t1 t2) (P t1' t2)"
commented out because of error
Type unification failed: Clash of types "_ \<Rightarrow> _" and "bool"

Type error in application: incompatible operand type

Operator:  Trueprop :: bool \<Rightarrow> prop
Operand:   t1 \<longrightarrow>* t1' :: tm \<Rightarrow> bool
*)

(* commented out because of error
lemma eval__multistep : "eval t n \<Longrightarrow> multi t C n"

Type unification failed: Clash of types "tm" and "_ \<Rightarrow> _"
*)
end