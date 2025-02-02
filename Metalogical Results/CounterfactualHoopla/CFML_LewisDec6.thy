theory CFML_LewisDec6
imports Main

begin
section \<open>* QCML- logic of counterfactuals *\<close>

  typedecl i    (* "the type for possible worlds" *)
  typedecl j    (* "the type for elements of a set" *)
  typedecl \<mu>    (* "the type for individuals"      *)
  type_synonym \<sigma> = "(i \<Rightarrow> bool)"  
  
  
  consts r :: " i \<Rightarrow>((i \<times> i) \<Rightarrow> bool)"  (* "world ordering relations r_w"  *)
  consts Ww :: "i \<Rightarrow> i set"  (*Set W_w *)

  axiomatization where domr: " \<forall>w x y. r w (x,y) \<longrightarrow> (x \<in> Ww(w) \<and> y \<in> Ww(w) )" (*Making r a relation over Ww *)
  
  axiomatization where
  r_Ww_coherence: "\<forall>w x y. r w (x,y) \<longrightarrow> (x \<in> Ww(w) \<longleftrightarrow> y \<in> Ww(w))"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<not>") where "\<^bold>\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"
  abbreviation mnegpred :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>(\<mu>\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53)  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"  
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<and>" 51) where "\<phi> \<^bold>\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<or>" 50) where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<rightarrow>" 49) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 48) where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"
  abbreviation mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mexistsB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "\<^bold>=\<^sup>L" 52) where "x \<^bold>=\<^sup>L y \<equiv> \<^bold>\<forall>(\<lambda>\<phi>. (\<phi> x \<^bold>\<rightarrow> \<phi> y))"
  
  abbreviation KMin :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" where "KMin(\<phi>)(\<psi>) \<equiv>  \<lambda>w. (\<exists>v.  (((\<phi> v \<and> (v\<in>Ww(w))) \<and> (\<forall>u. ((r w (u, v)) \<longrightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) u))))    ))"

    
  consts mcbox :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<box>\<rightarrow>" 70)
  consts mcdia :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>"  (infixr "\<diamond>\<rightarrow>" 70)
  

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*)
    
    
(* Defining Semantics of counterfactuals*)
abbreviation LewisVC 
  where "LewisVC \<equiv> \<forall>\<phi> \<psi>. \<forall>w. (\<phi> \<box>\<rightarrow> \<psi>)(w) \<longleftrightarrow> (( \<not>( \<exists>v\<in>Ww(w). \<phi> v)  ) \<or> KMin(\<phi>)(\<psi>)(w))"        


(*Some metalogical Operators for Kripke frames*)    
abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") 
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation follows_w :: "i \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix"\<^bold>\<Turnstile>"55)
  where "(w  \<^bold>\<Turnstile> p)  \<equiv> p w  "
abbreviation follows_glob :: "bool \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix"\<^bold>\<turnstile>"40)
  where "(L \<^bold>\<turnstile> p )  \<equiv> (L \<longrightarrow> \<lfloor>p\<rfloor>)"

(*Conversion into Normal Modal Logic*)
abbreviation bottom :: "\<sigma>" ("\<bottom>") 
  where "\<bottom> (w) \<equiv> w \<^bold>\<Turnstile>(\<^bold>\<exists> \<Phi>. (\<^bold>\<not>\<Phi>  \<^bold>\<and>  \<Phi>))"
abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>") where "\<^bold>\<box> \<phi> \<equiv> ( (\<^bold>\<not>\<phi>)\<box>\<rightarrow> \<bottom>)"

(*Minsets *)
definition Lew_Minset :: "i \<Rightarrow> \<sigma> \<Rightarrow> i set" where
    " Lew_Minset w \<phi> = {v. (v\<in>Ww(w) ) \<and> (v \<^bold>\<Turnstile> \<phi>) \<and> (\<forall>u. ((u\<^bold>\<Turnstile> \<phi>)\<longrightarrow> (r w (v, u)) )) } "

  
(*Constraints for order relation*)    
abbreviation reflexive :: "i \<Rightarrow>bool"
  where "reflexive \<equiv> (\<lambda>w. \<forall>x. x\<in> Ww(w) \<longrightarrow> (r w (x, x)))"
abbreviation symmetric 
  where "symmetric \<equiv> (\<lambda>w. \<forall>x y. (r w (x,y)) \<longrightarrow>  (r w (y, x)) )"
abbreviation transitive :: "i \<Rightarrow> bool"
  where "transitive \<equiv> (\<lambda>w. \<forall>x y z. ((r w (x, y) \<and> r w (y, z)) \<longrightarrow> (r w (x, z))))" 
abbreviation finiteWorlds :: "bool"
  where "finiteWorlds \<equiv> finite (UNIV :: i set)"
    
(*Constraints for counterfactuals*)
abbreviation Preorder
 where "Preorder  \<equiv> \<forall>w. reflexive(w) \<and> transitive(w)"
abbreviation Total :: "i \<Rightarrow>bool"
  where "Total \<equiv> (\<lambda>w. \<forall>x y. ( r w (x, y) \<or> r w (y, x) ) )"

subsection \<open>* Syntax Correspondence *\<close>

axiomatization  where 
      Preorder: "Preorder" and
      totale: "\<forall>w. Total(w)" and
      LVC: "LewisVC" 
      
axiomatization where Cent: "\<forall>w. {w} = Lew_Minset w (\<^bold>\<not> \<bottom>)"      
      
(*Lewis's System VC*)

lemma K0: "\<lfloor>\<^bold>\<box>(\<phi>  \<^bold>\<rightarrow> \<psi>)  \<^bold>\<rightarrow> ( (\<^bold>\<box>\<phi>)  \<^bold>\<rightarrow> (\<^bold>\<box> \<psi>) ) \<rfloor>"
  using LVC by metis

lemma K1: "True \<^bold>\<turnstile> p \<longrightarrow> \<lfloor>\<^bold>\<box>p \<rfloor>"
  using Preorder by metis

lemma L1: "\<lfloor>\<phi> \<box>\<rightarrow> \<phi>\<rfloor>"
  using LVC Preorder domr by metis

lemma L2: "\<lfloor>((\<^bold>\<not>\<phi>) \<box>\<rightarrow> \<phi>)  \<^bold>\<rightarrow> (\<psi> \<box>\<rightarrow> \<phi>) \<rfloor>"
  using LVC Preorder domr by metis

(*Counterexample failed 58/90 timout 300 *)
 lemma L3: "\<lfloor>(\<phi> \<box>\<rightarrow> (\<^bold>\<not>\<psi>))  \<^bold>\<or> (((\<psi> \<^bold>\<and> \<phi>) \<box>\<rightarrow> \<zeta>)  \<^bold>\<leftrightarrow> (\<phi> \<box>\<rightarrow>  (\<psi> \<^bold>\<rightarrow> \<zeta>) )) \<rfloor>"
   using Cent LVC totale Preorder Lew_Minset_def domr r_Ww_coherence by metis

(*
(*Proof found by spass cvc4 *)
lemma L4: "\<lfloor>((\<phi>) \<box>\<rightarrow> \<psi>)  \<^bold>\<rightarrow> (\<phi>  \<^bold>\<rightarrow> \<psi>) \<rfloor>"
  using LVC Cent  by blast 

(*Counterexample failed 42/90 timout 100 *)
(*Proof found by zipperposition *)
lemma L5: "\<lfloor>((\<psi> \<^bold>\<and> \<phi>)  \<^bold>\<rightarrow> (\<phi> \<box>\<rightarrow>  \<psi>)) \<rfloor> "
  using LVC Cent by blast *)

(*Consistency check *)
lemma True
  nitpick[satisfy, user_axioms, expect = genuine] oops

end
