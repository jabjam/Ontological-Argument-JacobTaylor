
theory Anderson_var
imports Main "../QML_var"

begin

(*Note sigma sends individuals to bool typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals" *)

section \<open>* Anderson's Ontological Argument -- varying domain (individuals) *\<close>

consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  
  type_synonym \<zeta> = "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"
            
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )"  
            
definition NotEq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where
  "NotEq x y \<equiv> \<^bold>\<not>(x \<^bold>=\<^sup>L y)"
  
  
datatype 'a ModalVars =
  Some "\<mu>" | "i"
  
datatype 'a Nest_formula = 
   CR "'a ModalVars"  
  | MEq "'a ModalVars" "'a ModalVars"
  | MNot "'a Nest_formula"         
  | MAnd "'a Nest_formula" "'a Nest_formula" 
    
 (*Getting set of individuals from a Nested formula*)
  fun term_vars :: "'a Nest_formula \<Rightarrow> 'a ModalVars set" where
  "term_vars (CR x) = {x}"|
  "term_vars (MEq x y) = {x} \<union> {y}"
  | "term_vars (MAnd t1 t2) = term_vars t1 \<union> term_vars t2"
  | "term_vars (MNot p) = term_vars p"
  
  
consts H :: "\<mu> \<Rightarrow> \<sigma>"
  
  
consts U1 :: "\<mu> \<Rightarrow> \<sigma>" (*Horn property- true for narwals *)
consts U2 :: "\<mu> \<Rightarrow> \<sigma>" (*Horse property*)
consts U3 :: "\<mu> \<Rightarrow> \<sigma>" (*Lives in Switzerland*)

axiomatization where
    (*A1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"  and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" and
    B3:  "\<lfloor>P H\<rfloor>" and *)
    B4:  "\<exists>x y.  x r x \<and> x\<noteq>y" and (*More than one world *)
    B5:  "\<exists>w. (w r w) \<and> ((\<^bold>\<exists>\<^sup>Ex. (\<^bold>\<exists>\<^sup>Ey. (\<^bold>\<not>(x \<^bold>=\<^sup>L y))) ) w)"   (*world with more than one individual *)
    
 
(* axiomatization where 
    Unicorns1 :  "\<lfloor>\<^bold>\<exists> \<Phi>. \<^bold>\<forall>\<^sup>Ex.(\<Phi> x \<^bold>\<leftrightarrow>  U1 x) \<rfloor>"    and
    Unicorns2 :  "\<lfloor>\<^bold>\<exists> \<Phi>. \<^bold>\<forall>\<^sup>Ex.(\<Phi> x \<^bold>\<leftrightarrow>  U2 x)\<rfloor>"  and
    Unicorns3 :  "\<lfloor>\<^bold>\<exists> \<Phi>. \<^bold>\<forall>\<^sup>Ex.(\<Phi> x \<^bold>\<leftrightarrow>  U3 x)\<rfloor>"   *)

definition D :: "\<mu> \<Rightarrow> \<sigma>" where
  " D (x) \<equiv> \<^bold>\<not>(U1(x)  \<^bold>\<and> U2(x)  \<^bold>\<and> U3 (x))"
  
definition DL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DL (x) \<equiv> \<^bold>\<not>(D(x))"  
    
definition Perfective1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))"  
    
definition Perfective2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"      
  
definition Perfective ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Perfective (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  D(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  D(x) )))"
    

subsection \<open>* Consistency *\<close>

  lemma True 
    nitpick [satisfy, user_axioms, expect = genuine] oops
      
subsection \<open>* HOL *\<close>

(*Proof found,/nitpick failed *)
theorem Pred: "\<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> x \<^bold>\<leftrightarrow>  (\<^bold>\<exists>\<^sup>Ey. (x \<^bold>=\<^sup>L y) ))\<rfloor>"
  using nonempty by blast

(* proof -
  obtain ii :: i where
    f1: "(\<exists>X0. \<forall>x1. (X0 \<^bold>\<Turnstile> (\<^sup>\<not>x1) x \<or> (\<forall>A_x. X0 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) A_x \<or> (\<exists>x3. X0 \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> X0 \<^bold>\<Turnstile> x3 x))) \<and> (X0 \<^bold>\<Turnstile> x1 x \<or> (\<exists>x4. X0 \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. X0 \<^bold>\<Turnstile> x5 x4 \<or> X0 \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)))) \<longrightarrow> (\<forall>x1. (ii \<^bold>\<Turnstile> (\<^sup>\<not>x1) x \<or> (\<forall>A_x. ii \<^bold>\<Turnstile> (\<^sup>\<not>eiw) A_x \<or> (\<exists>x3. ii \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> ii \<^bold>\<Turnstile> x3 x))) \<and> (ii \<^bold>\<Turnstile> x1 x \<or> (\<exists>x4. ii \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 x4 \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x))))"
    by metis
  obtain bb :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
    f2: "\<forall>A_x. (\<exists>x3. ii \<^bold>\<Turnstile> (\<^sup>\<not>x3) A_x \<and> ii \<^bold>\<Turnstile> x3 x) \<longrightarrow> ii \<^bold>\<Turnstile> (\<^sup>\<not>bb A_x) A_x \<and> ii \<^bold>\<Turnstile> bb A_x x"
    by moura
  obtain mm :: \<mu> where
    f3: "(\<exists>x4. ii \<^bold>\<Turnstile> eiw x4 \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 x4 \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)) \<longrightarrow> ii \<^bold>\<Turnstile> eiw mm \<and> (\<forall>x5. ii \<^bold>\<Turnstile> x5 mm \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>x5) x)"
    by presburger
  have "\<exists>p. ii \<^bold>\<Turnstile> p x \<and> (\<exists>m. ii \<^bold>\<Turnstile> eiw m \<and> (ii \<^bold>\<Turnstile> bb m m \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>bb m) x)) \<or> ii \<^bold>\<Turnstile> (\<^sup>\<not>p) x \<and> (ii \<^bold>\<Turnstile> (\<^sup>\<not>eiw) mm \<or> (\<exists>p. ii \<^bold>\<Turnstile> (\<^sup>\<not>p) mm \<and> ii \<^bold>\<Turnstile> p x))"
    by meson (* > 1.0 s, timed out *)
  then have "\<lfloor>\<lambda>i. \<exists>p. i \<^bold>\<Turnstile> p x \<and> (\<exists>m. i \<^bold>\<Turnstile> eiw m \<and> (\<forall>p. i \<^bold>\<Turnstile> p m \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) x)) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) x \<and> (\<forall>m. i \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> (\<exists>p. i \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<and> i \<^bold>\<Turnstile> p x))\<rfloor>"
    using f3 f2 f1 by moura (* > 1.0 s, timed out *)
  then show ?thesis
    by (metis (no_types))
qed*)

(*Proof found,/nitpick failed *)    
theorem Taut: " L \<^bold>\<turnstile> p \<Longrightarrow> \<lfloor>\<^bold>\<exists>\<Phi>.( \<Phi> \<^bold>\<leftrightarrow>  p )\<rfloor>"
  using nonempty by blast
    
section \<open>* Perfective *\<close>    
 
axiomatization where refl: "x r x"
axiomatization where sym: "x r y \<longrightarrow> y r x"  
axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
  
lemma PConjun: "\<lfloor> Perfective(\<phi>)  \<^bold>\<leftrightarrow> (Perfective1(\<phi>) \<^bold>\<and> Perfective2(\<phi>)) \<rfloor>"
  apply (metis Perfective1_def Perfective2_def Perfective_def)
  prf
  done
  
    
(*Note that the Isar proof works for when D is simply a consts*)    
lemma Giv: "\<lfloor>Perfective1 DL\<rfloor>"
  apply (metis DL_def D_def Perfective1_def)
  prf
  done
    
  (*proof -
  obtain ii :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i" where
    "\<lfloor>\<lambda>x0. \<forall>x1. x0 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>v2. \<exists>v3. (v2 \<^bold>\<Turnstile> eiw v3 \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> v2 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3) = (ii x0 x1 \<^bold>\<Turnstile> op r x0 \<and> (\<exists>v3. (ii x0 x1 \<^bold>\<Turnstile> eiw v3 \<and> ii x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>x1) v3) \<and> ii x0 x1 \<^bold>\<Turnstile> (\<^sup>\<not>D) v3))\<rfloor>"
    by moura
  then obtain mm :: "i \<Rightarrow> (\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<mu>" where
    "\<forall>p. \<lfloor>\<lambda>i. (i \<^bold>\<Turnstile> \<^bold>\<not> (Perfective1 p) \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> (op r i) \<or> (\<forall>m. (ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) m \<or> ia \<^bold>\<Turnstile> p m) \<or> ia \<^bold>\<Turnstile> D m)\<rfloor>) \<and> (i \<^bold>\<Turnstile> Perfective1 p \<or> ii i p \<^bold>\<Turnstile> op r i \<and> (ii i p \<^bold>\<Turnstile> eiw (mm i p) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>p) (mm i p)) \<and> ii i p \<^bold>\<Turnstile> (\<^sup>\<not>D) (mm i p))\<rfloor>"
    by (metis (full_types) Perfective1_def)
  then show ?thesis
    by (metis (full_types) DL_def)
qed*)

lemma PN: "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  nitpick oops

lemma PN1: "\<lfloor>Perfective(\<phi>) \<^bold>\<rightarrow> (Perfective1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  nitpick oops

lemma Giv2: "\<lfloor>Perfective2 DL\<rfloor>"
  nitpick[user_axioms] oops

(*Section:  Perfective V2*) 

consts OP :: "\<mu> \<Rightarrow> \<sigma>"

definition DN :: "\<mu> \<Rightarrow> \<sigma>" where
  " DN (x) \<equiv> \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( OP(y)) ))(x)  )"
  
definition DNL :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNL (x) \<equiv> \<^bold>\<not>(DN(x))"  
    
definition Pn1 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))"  
    
definition Pn2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"      
  
definition PerfectiveV2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV2 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN(x) )))"


lemma PN1Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn1 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
nitpick [user_axioms, show_all] oops


lemma PN2Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
 nitpick [user_axioms] oops

(*Perfective V2- Onioned out *)

definition DNO :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNO (x) \<equiv> \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )"
  
definition DNLO :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNLO (x) \<equiv> \<^bold>\<not>(DNO(x))"  
    
definition Pn1O ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1O (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow> ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )  ) ) ))"  
    
definition Pn2O ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2O (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )) )))"      
  
definition PerfectiveV2O ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV2O (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow> ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )) )))"


lemma PN1Attempt2: "\<lfloor>( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow> ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  
( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )) ))) \<^bold>\<rightarrow> (( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( ( ( \<lambda>x. \<^bold>\<not> ( \<^bold>\<box> (\<phi>(x)))) (x)) \<^bold>\<rightarrow> ( \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> (OP(y)) ))(x)  )  ) ) )))\<rfloor>"

  nitpick [user_axioms] oops


lemma PN2Attempt2: "\<lfloor>PerfectiveV2(\<phi>) \<^bold>\<rightarrow> (Pn2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
 nitpick [user_axioms] oops

(*Subsection:  Perfective V3- Affect*)

consts Affect :: "(\<mu>  \<times> \<mu> \<times> \<mu>) \<Rightarrow> \<sigma>"
consts Physical :: "(\<mu>) \<Rightarrow> \<sigma>"

axiomatization where 
Affectasymm : "\<lfloor>  \<^bold>\<not>(y \<^bold>=\<^sup>L x)  \<^bold>\<rightarrow>(Affect(x,y,Q) \<^bold>\<rightarrow> \<^bold>\<not> (Affect(y,x,Q)))\<rfloor>" and
Affectexist : "\<lfloor>Affect(x,y,Q) \<^bold>\<rightarrow>  (eiw x  \<^bold>\<and> eiw y  \<^bold>\<and> eiw Q)\<rfloor> " and
Affect_possible: "\<lfloor>(eiw x  \<^bold>\<and> eiw y  \<^bold>\<and> eiw Q)  \<^bold>\<rightarrow> (Affect(x,y,Q)  \<^bold>\<rightarrow> \<^bold>\<diamond> (Affect(x,y,Q)))\<rfloor>" and
Affect_stable: "\<lfloor>Affect(x,y,Q)  \<^bold>\<and> (eiw x  \<^bold>\<and> eiw y  \<^bold>\<and> eiw Q)   \<^bold>\<rightarrow> (\<^bold>\<box>  ( (eiw x  \<^bold>\<and> eiw y  \<^bold>\<and> eiw Q)  \<^bold>\<rightarrow> ( \<^bold>\<diamond> (Affect(x,y,Q)))))   \<rfloor>"
axiomatization where 
Physical_stable: "\<lfloor> Physical(x) \<^bold>\<rightarrow> (\<^bold>\<box> (Physical(x))) \<rfloor>"

axiomatization where
Affect_physical_witness: "\<lfloor>Affect(x,y,Q) \<^bold>\<rightarrow> (Physical(Q) \<^bold>\<and> eiw Q)\<rfloor>"

definition DN_new :: "\<mu> \<Rightarrow> \<sigma>" where
  "DN_new (x) \<equiv>  \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( \<^bold>\<forall>\<^sup>Ez. \<^bold>\<exists>\<^sup>EQ.  \<^bold>\<not>(z \<^bold>=\<^sup>L Q)  \<^bold>\<and>  \<^bold>\<not>(y \<^bold>=\<^sup>L Q)  \<^bold>\<and> Physical(z)   \<^bold>\<and> (  \<^bold>\<not>(y \<^bold>=\<^sup>L z)  \<^bold>\<rightarrow> (\<^bold>\<diamond> (Affect(y,z,Q)) ) ) ) ))(x)  )"

definition DNL_new :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNL_new (x) \<equiv> \<^bold>\<not>(DN_new(x))"  
    
definition Pn1V3 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1V3 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN_new(x) ) ))"  
    
definition Pn2V3 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2V3 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN_new(x) )))"      
  
definition PerfectiveV3 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveV3 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DN_new(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DN_new(x) )))"

consts K :: "\<mu>\<Rightarrow>\<sigma>"

axiomatization where Dawg :"\<lfloor> PerfectiveV3 K \<rfloor>"

lemma True 
   nitpick [satisfy, user_axioms, timeout=300, show_all, expect = genuine] oops

lemma PN1Attempt3: "\<lfloor>PerfectiveV3(\<phi>) \<^bold>\<rightarrow> (Pn1V3 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  nitpick[user_axioms, show_all, timeout =100] oops

(*Said proof found- vampire & cvc4 *)
lemma PN1Attempt3: "\<lfloor>PerfectiveV3(\<phi>) \<^bold>\<rightarrow> (Pn1V3 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  proof  -
  obtain ii :: i where
    f1: "(\<exists>X0. X0 \<^bold>\<Turnstile> \<^bold>\<not> (Pn1V3 (\<lambda>uu uua. uua \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>v. v \<^bold>\<Turnstile> \<phi> uu)))) \<longrightarrow> ii \<^bold>\<Turnstile> \<^bold>\<not> (Pn1V3 (\<lambda>uu uua. uua \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>v. v \<^bold>\<Turnstile> \<phi> uu)))"
    by blast
  obtain iia :: "\<mu> \<Rightarrow> i \<Rightarrow> i" where
    f2: "\<forall>X0. \<lfloor>\<lambda>X1. X1 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>A_x. \<exists>X3. A_x \<^bold>\<Turnstile> eiw X3 \<and> (\<forall>X4. (\<forall>X5. A_x \<^bold>\<Turnstile> (\<^sup>\<not>X5) X0 \<or> A_x \<^bold>\<Turnstile> X5 X4) \<or> (\<forall>X6. A_x \<^bold>\<Turnstile> X6 X4 \<or> A_x \<^bold>\<Turnstile> (\<^sup>\<not>X6) X3) \<or> (\<forall>X7. A_x \<^bold>\<Turnstile> X7 X4 \<or> A_x \<^bold>\<Turnstile> (\<^sup>\<not>X7) X0) \<or> A_x \<^bold>\<Turnstile> (\<^sup>\<not>eiw) X4 \<or> \<lfloor>\<lambda>X8. X8 \<^bold>\<Turnstile> \<^bold>\<not> ((r) A_x) \<or> X8 \<^bold>\<Turnstile> \<^bold>\<not> (Affect (X0, X3, X4))\<rfloor>)) \<longrightarrow> iia X0 X1 \<^bold>\<Turnstile> (r) X1 \<and> (\<exists>X3. iia X0 X1 \<^bold>\<Turnstile> eiw X3 \<and> (\<forall>X4. (\<forall>X5. iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X5) X0 \<or> iia X0 X1 \<^bold>\<Turnstile> X5 X4) \<or> (\<forall>X6. iia X0 X1 \<^bold>\<Turnstile> X6 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X6) X3) \<or> (\<forall>X7. iia X0 X1 \<^bold>\<Turnstile> X7 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X7) X0) \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) X4 \<or> \<lfloor>\<lambda>X8. X8 \<^bold>\<Turnstile> \<^bold>\<not> ((r) (iia X0 X1)) \<or> X8 \<^bold>\<Turnstile> \<^bold>\<not> (Affect (X0, X3, X4))\<rfloor>))\<rfloor>"
    by moura
  obtain mm :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu>" where
    f3: "\<forall>X0. \<lfloor>\<lambda>X1. (\<exists>X3. iia X0 X1 \<^bold>\<Turnstile> eiw X3 \<and> (\<forall>X4. (\<forall>X5. iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X5) X0 \<or> iia X0 X1 \<^bold>\<Turnstile> X5 X4) \<or> (\<forall>X6. iia X0 X1 \<^bold>\<Turnstile> X6 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X6) X3) \<or> (\<forall>X7. iia X0 X1 \<^bold>\<Turnstile> X7 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X7) X0) \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) X4 \<or> \<lfloor>\<lambda>X8. X8 \<^bold>\<Turnstile> \<^bold>\<not> ((r) (iia X0 X1)) \<or> X8 \<^bold>\<Turnstile> \<^bold>\<not> (Affect (X0, X3, X4))\<rfloor>)) \<longrightarrow> iia X0 X1 \<^bold>\<Turnstile> eiw (mm X0 X1) \<and> (\<forall>X4. (\<forall>X5. iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X5) X0 \<or> iia X0 X1 \<^bold>\<Turnstile> X5 X4) \<or> (\<forall>X6. iia X0 X1 \<^bold>\<Turnstile> X6 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X6) (mm X0 X1)) \<or> (\<forall>X7. iia X0 X1 \<^bold>\<Turnstile> X7 X4 \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>X7) X0) \<or> iia X0 X1 \<^bold>\<Turnstile> (\<^sup>\<not>eiw) X4 \<or> \<lfloor>\<lambda>X8. X8 \<^bold>\<Turnstile> \<^bold>\<not> ((r) (iia X0 X1)) \<or> X8 \<^bold>\<Turnstile> \<^bold>\<not> (Affect (X0, mm X0 X1, X4))\<rfloor>)\<rfloor>"
    by moura
  obtain mma :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu>" where
    f4: "\<forall>X0. \<lfloor>\<lambda>X9. \<forall>X10. (\<exists>X11. (\<exists>X12. X9 \<^bold>\<Turnstile> X12 X0 \<and> X9 \<^bold>\<Turnstile> (\<^sup>\<not>X12) X11) \<and> (\<exists>X13. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X13) X11 \<and> X9 \<^bold>\<Turnstile> X13 X10) \<and> (\<exists>X14. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X14) X11 \<and> X9 \<^bold>\<Turnstile> X14 X0) \<and> X9 \<^bold>\<Turnstile> eiw X11 \<and> X9 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>X15. X15 \<^bold>\<Turnstile> Affect (X0, X10, X11))) \<longrightarrow> (\<exists>X12. X9 \<^bold>\<Turnstile> X12 X0 \<and> X9 \<^bold>\<Turnstile> (\<^sup>\<not>X12) (mma X0 X9 X10)) \<and> (\<exists>X13. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X13) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> X13 X10) \<and> (\<exists>X14. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X14) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> X14 X0) \<and> X9 \<^bold>\<Turnstile> eiw (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>X15. X15 \<^bold>\<Turnstile> Affect (X0, X10, mma X0 X9 X10))\<rfloor>"
    by moura
  obtain bb :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
    f5: "\<forall>X0. \<lfloor>\<lambda>X9. \<forall>X10. (\<exists>X12. X9 \<^bold>\<Turnstile> X12 X0 \<and> X9 \<^bold>\<Turnstile> (\<^sup>\<not>X12) (mma X0 X9 X10)) \<longrightarrow> X9 \<^bold>\<Turnstile> bb X0 X9 X10 X0 \<and> X9 \<^bold>\<Turnstile> (\<^sup>\<not>bb X0 X9 X10) (mma X0 X9 X10)\<rfloor>"
    by moura
  obtain bba :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
    f6: "\<forall>X0. \<lfloor>\<lambda>X9. \<forall>X10. (\<exists>X13. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X13) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> X13 X10) \<longrightarrow> X9 \<^bold>\<Turnstile> (\<^sup>\<not>bba X0 X9 X10) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> bba X0 X9 X10 X10\<rfloor>"
    by moura
  obtain bbb :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
    f7: "\<forall>X0. \<lfloor>\<lambda>X9. \<forall>X10. (\<exists>X14. X9 \<^bold>\<Turnstile> (\<^sup>\<not>X14) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> X14 X0) \<longrightarrow> X9 \<^bold>\<Turnstile> (\<^sup>\<not>bbb X0 X9 X10) (mma X0 X9 X10) \<and> X9 \<^bold>\<Turnstile> bbb X0 X9 X10 X0\<rfloor>"
    by moura
  obtain iib :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> i" where
    f8: "\<forall>X0. \<lfloor>\<lambda>X9. \<forall>X10. X9 \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>X15. X15 \<^bold>\<Turnstile> Affect (X0, X10, mma X0 X9 X10)) \<longrightarrow> iib X0 X9 X10 \<^bold>\<Turnstile> ((r) X9 \<^bold>\<and> Affect (X0, X10, mma X0 X9 X10))\<rfloor>"
    by moura
  have "\<forall>p. \<lfloor>\<lambda>i. i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>DN_new) m \<and> i \<^bold>\<Turnstile> eiw m) \<or> i \<^bold>\<Turnstile> Pn1V3 p\<rfloor>"
    using Pn1V3_def by auto
  then obtain mmb :: "(\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> \<mu>" and iic :: "(\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i" and iid :: "(\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i" and mmc :: "(\<mu> \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> \<mu>" where
    f9: "\<forall>p. \<lfloor>\<lambda>i. iic p i \<^bold>\<Turnstile> (r) i \<and> iic p i \<^bold>\<Turnstile> (\<^sup>\<not>p) (mmb p i) \<and> iic p i \<^bold>\<Turnstile> (\<^sup>\<not>DN_new) (mmb p i) \<and> iic p i \<^bold>\<Turnstile> eiw (mmb p i) \<or> i \<^bold>\<Turnstile> Pn1V3 p\<rfloor>"
    by moura
  have "\<forall>m. \<lfloor>\<lambda>i. (i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>ma. i \<^bold>\<Turnstile> eiw ma \<and> (\<forall>mb. (\<forall>p. i \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<or> i \<^bold>\<Turnstile> p mb) \<or> (\<forall>p. i \<^bold>\<Turnstile> p mb \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) ma) \<or> (\<forall>p. i \<^bold>\<Turnstile> p mb \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>p) m) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>eiw) mb \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> ((r) i) \<or> ia \<^bold>\<Turnstile> \<^bold>\<not> (Affect (m, ma, mb))\<rfloor>)) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>DN_new) m) \<and> (i \<^bold>\<Turnstile> DN_new m \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> ((r) i) \<or> (\<forall>ma. ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) ma \<or> (\<exists>mb. (\<exists>p. ia \<^bold>\<Turnstile> p m \<and> ia \<^bold>\<Turnstile> (\<^sup>\<not>p) mb) \<and> (\<exists>p. ia \<^bold>\<Turnstile> (\<^sup>\<not>p) mb \<and> ia \<^bold>\<Turnstile> p ma) \<and> (\<exists>p. ia \<^bold>\<Turnstile> (\<^sup>\<not>p) mb \<and> ia \<^bold>\<Turnstile> p m) \<and> ia \<^bold>\<Turnstile> eiw mb \<and> ia \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. i \<^bold>\<Turnstile> Affect (m, ma, mb))))\<rfloor>)\<rfloor>"
    by (smt (z3) DN_new_def) (* > 1.0 s, timed out *)
  then obtain iie :: "\<mu> \<Rightarrow> i \<Rightarrow> i" and mmd :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu>" and bbc :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" and mme :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu>" and bbd :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" and bbe :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" and iif :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> i" where
    "\<forall>m. \<lfloor>\<lambda>i. (iie m i \<^bold>\<Turnstile> (r) i \<and> iie m i \<^bold>\<Turnstile> eiw (mmd m i) \<and> (\<forall>ma. (\<forall>p. iie m i \<^bold>\<Turnstile> (\<^sup>\<not>p) m \<or> iie m i \<^bold>\<Turnstile> p ma) \<or> (\<forall>p. iie m i \<^bold>\<Turnstile> p ma \<or> iie m i \<^bold>\<Turnstile> (\<^sup>\<not>p) (mmd m i)) \<or> (\<forall>p. iie m i \<^bold>\<Turnstile> p ma \<or> iie m i \<^bold>\<Turnstile> (\<^sup>\<not>p) m) \<or> iie m i \<^bold>\<Turnstile> (\<^sup>\<not>eiw) ma \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> ((r) (iie m i)) \<or> ia \<^bold>\<Turnstile> \<^bold>\<not> (Affect (m, mmd m i, ma))\<rfloor>) \<or> i \<^bold>\<Turnstile> (\<^sup>\<not>DN_new) m) \<and> (i \<^bold>\<Turnstile> DN_new m \<or> \<lfloor>\<lambda>ia. ia \<^bold>\<Turnstile> \<^bold>\<not> ((r) i) \<or> (\<forall>ma. ia \<^bold>\<Turnstile> (\<^sup>\<not>eiw) ma \<or> (ia \<^bold>\<Turnstile> bbc m ia ma m \<and> ia \<^bold>\<Turnstile> (\<^sup>\<not>bbc m ia ma) (mme m ia ma)) \<and> (ia \<^bold>\<Turnstile> (\<^sup>\<not>bbd m ia ma) (mme m ia ma) \<and> ia \<^bold>\<Turnstile> bbd m ia ma ma) \<and> (ia \<^bold>\<Turnstile> (\<^sup>\<not>bbe m ia ma) (mme m ia ma) \<and> ia \<^bold>\<Turnstile> bbe m ia ma m) \<and> ia \<^bold>\<Turnstile> eiw (mme m ia ma) \<and> iif m ia ma \<^bold>\<Turnstile> ((r) ia \<^bold>\<and> Affect (m, ma, mme m ia ma)))\<rfloor>)\<rfloor>"
    using f8 f7 f6 f5 f4 f3 f2 by (smt (z3)) (* > 1.0 s, timed out *)
  then have "iic (\<lambda>m i. i \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>i. i \<^bold>\<Turnstile> \<phi> m)) ii \<^bold>\<Turnstile> (eiw (mmb (\<lambda>m i. i \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>i. i \<^bold>\<Turnstile> \<phi> m)) ii) \<^bold>\<rightarrow> DN_new (mmb (\<lambda>m i. i \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>i. i \<^bold>\<Turnstile> \<phi> m)) ii))"
    by (meson Affectasymm Anderson_var.refl)
  then have "ii \<^bold>\<Turnstile> Pn1V3 (\<lambda>m i. i \<^bold>\<Turnstile> \<^bold>\<box> (\<lambda>i. i \<^bold>\<Turnstile> \<phi> m))"
    using f9 by meson
  then show ?thesis
    using f1 by blast
qed 
  
  
  (*using refl trans sym Pn1V3_def DN_new_def PerfectiveV3_def  Affectasymm  
     by (meson Affectasymm Anderson_var.sym Anderson_var.trans DN_new_def Pn1V3_def) *)
  (*nitpick[user_axioms, timeout = 3600] oops *)

(*Isar proof *)

(*    *)

(*vampire and vcv4 found proof *)
lemma PN2Attempt3: "\<lfloor>PerfectiveV3(\<phi>) \<^bold>\<rightarrow> (Pn2V3 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  using refl trans sym Pn2V3_def DN_new_def PerfectiveV3_def  Affectasymm by blast
 (* nitpick [user_axioms, timeout = 3600] oops *)

(* lemma PConjun2: "\<lfloor> PerfectiveV3(\<phi>)  \<^bold>\<leftrightarrow> ((Pn1V3(\<phi>)) \<^bold>\<and>  (Pn2V3(\<phi>))) \<rfloor>"
  apply (metis  Pn1V3_def Pn2V3_def PerfectiveV3_def)
  prf
  done *)


(*theorem PN: "\<lfloor>PerfectiveV3(\<phi>) \<^bold>\<rightarrow> (PerfectiveV3(\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor> "
 apply (metis PN1Attempt3 PN2Attempt3 PConjun2 PerfectiveV3_def)
 prf
 done *)

(*Subsection:  Variants- Affect-1*)


definition DNffect :: "\<mu> \<Rightarrow> \<sigma>" where
  "DNffect (x) \<equiv>  \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( \<^bold>\<forall>\<^sup>Ez. \<^bold>\<forall>\<^sup>EQ. ( \<^bold>\<not>(z \<^bold>=\<^sup>L Q)  \<^bold>\<and>  \<^bold>\<not>(y \<^bold>=\<^sup>L Q))  \<^bold>\<rightarrow>  (\<^bold>\<diamond> (Affect(y,z,Q)) ) ) ))(x)  )"

definition DNLffect :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNLffect (x) \<equiv> \<^bold>\<not>(DNffect(x))"  
    
definition Pn1ffect ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1ffect (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DNffect(x) ) ))"  
    
definition Pn2ffect ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2ffect (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DNffect(x) )))"      
  
definition PerfectiveVffect ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveVffect (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DNffect(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DNffect(x) )))"


(*Nitpick checked 112 of 890 scopes*)
lemma PN1ffect: "\<lfloor>PerfectiveVffect(\<phi>) \<^bold>\<rightarrow> (Pn1ffect (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  using refl trans sym Pn1ffect_def DNffect_def PerfectiveVffect_def  Affectasymm  
     by blast
    (* nitpick[user_axioms, timeout = 3600] oops *)  


lemma PN2ffect: "\<lfloor>PerfectiveVffect(\<phi>) \<^bold>\<rightarrow> (Pn2ffect (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  using refl trans sym Pn2ffect_def DNffect_def PerfectiveVffect_def  Affectasymm by blast
 (* nitpick [user_axioms, timeout = 3600] oops *)

(*Subsection:  Variants- Affect-2*)

consts Affect_var :: "(\<mu> \<times> \<mu>) \<Rightarrow> \<sigma>"

axiomatization where Affectasymm2 : "\<lfloor>Affect_var(x,y) \<^bold>\<rightarrow> \<^bold>\<not> (Affect_var(y,x))\<rfloor>"


definition DNffect2 :: "\<mu> \<Rightarrow> \<sigma>" where
  "DNffect2 (x) \<equiv>  \<^bold>\<not>( (\<lambda>y.  (\<^bold>\<box> ( \<^bold>\<forall>\<^sup>Ez.  (\<^bold>\<diamond> (Affect_var(y,z)) ) ) ))(x)  )"

definition DNLffect2 :: "\<mu> \<Rightarrow> \<sigma>" where
  " DNLffect2 (x) \<equiv> \<^bold>\<not>(DNffect2(x))"  
    
definition Pn1ffect2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn1ffect2 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DNffect2(x) ) ))"  
    
definition Pn2ffect2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  Pn2ffect2 (\<phi>)  \<equiv>  \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DNffect2(x) )))"      
  
definition PerfectiveVffect2 ::  "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where 
    "  PerfectiveVffect2 (\<phi>)  \<equiv> ( \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( (\<^bold>\<not> (\<phi>(x))) \<^bold>\<rightarrow>  DNffect2(x) ) ))  \<^bold>\<and>   \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<phi>(x) \<^bold>\<rightarrow>  DNffect2(x) )))"


lemma PN1ffect: "\<lfloor>PerfectiveVffect2(\<phi>) \<^bold>\<rightarrow> (Pn1ffect2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  using refl trans sym Pn1ffect2_def DNffect2_def PerfectiveVffect2_def  Affectasymm2 
     by (meson Affectasymm2 Anderson_var.sym Anderson_var.trans DNffect2_def Pn1ffect2_def)
  (*nitpick[user_axioms, timeout = 3600] oops *)


lemma PN2ffect: "\<lfloor>PerfectiveVffect2(\<phi>) \<^bold>\<rightarrow> (Pn2ffect2 (\<lambda>x. \<^bold>\<box> (\<phi>(x)) ))\<rfloor>"
  using refl trans sym Pn2ffect2_def DNffect2_def PerfectiveVffect2_def  Affectasymm2 by blast
 (* nitpick [user_axioms, timeout = 3600] oops *)

(*Subsection: Provability of T1, C and T3 *)
  
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  apply (metis A1 A2)
  prf
  done
  
  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  apply (metis T1 A3)
  prf
  done
  
lemma EP: "\<lfloor>P eiw\<rfloor>" (*Existence is positive *)
  apply (metis A2 B3)
  prf
  done
  (*proof -
    { fix ii :: i
      have "\<lfloor>\<lambda>i. \<forall>p pa. (i \<^bold>\<Turnstile> \<^bold>\<not> (P p) \<or> i \<^bold>\<Turnstile> \<^bold>\<diamond> (\<lambda>i. \<exists>m. i \<^bold>\<Turnstile> eiw m \<and> i \<^bold>\<Turnstile> p m \<and> i \<^bold>\<Turnstile> (\<^sup>\<not>pa) m)) \<or> i \<^bold>\<Turnstile> P pa\<rfloor>"
        by (metis A2)
      then have "ii \<^bold>\<Turnstile> P eiw"
        using A3 by blast }
    then show ?thesis
      by auto
  qed*)
  
    
  text {* we only need axiom B here *} 
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
    by (meson A3 Anderson_var.sym C1 EP G_def)

  (* sledgehammer [remote_satallax remote_leo2] *)


subsection {* Consistency again (now with sym) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of A4 and A5 *}

  text {* As noted by Petr Hajek, A4 and A5 can be derived
          from the other axioms and definitions. *}
  
  text {* for A4 we need transitivity *}
  

  theorem A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans T3)

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv> \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  theorem A5: "\<lfloor>P NE\<rfloor>"
  by (metis A2 A3 ess_def NE_def)


subsection {* Consistency again (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.((\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)))\<rfloor>"
  nitpick [user_axioms] oops

subsection {* Varia *}

lemma HAJEK: "\<lfloor>P ( \<lambda>x. (G x \<^bold>\<and> eiw x))\<rfloor>"
  by (metis A2 A3 A5)
    
    
 theorem TE: "\<lfloor>\<^bold>\<not> (\<^bold>\<forall>\<Phi>. (\<^bold>\<not>(\<^bold>\<forall>\<^sup>Ex.  \<Phi> x  \<^bold>\<leftrightarrow>  (eiw x) ) ))\<rfloor>"
    by (metis nonempty) 


  lemma PEP: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> (\<lambda>x. (\<Phi> = \<Psi>))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

  lemma PEP_Leibniz: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> (\<^bold>\<forall>Q.(Q \<Phi> \<^bold>\<rightarrow> Q \<Psi>  ))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

  lemma weak_congruence: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> \<^bold>\<box>(\<lambda>x. (\<Phi> = \<Psi>))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A2) 


end
