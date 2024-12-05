theory Anderson_CML_Best
imports Main "../CFML_Lewis_var"

begin


section ‹* Taylor's Ontological Argument -- Counterfactuals *›

consts P :: "(μ ⇒ σ) ⇒ σ"  
  
definition G :: "μ ⇒ σ" where 
            "G x ≡ ❙∀Φ.( P Φ ❙↔  ( (❙□ (Φ x ))) )"  
            
definition NotEq :: "μ ⇒ μ ⇒ σ" where
  "NotEq x y ≡ ❙¬(x ❙=⇧L y)"
  
consts H :: "μ ⇒ σ"
type_synonym z = " μ ⇒ σ"
  
axiomatization where
    CF1: "Preorder" and
    CF2: "∀w. Total(w)" and
    CF3: "LewisVC"


(* axiomatization where
    A1:  "⌊❙∀Φ. (((P Φ) ❙→ ❙¬ (P (⇧¬Φ)) )  )⌋"  and
    A2:  "⌊❙∀Φ.( ❙∀Ψ.( ( (P Φ) ❙∧ ❙□ (❙∀⇧Ex.( Φ x ❙→ Ψ x))) ❙→ P Ψ))⌋" and
    A3:  "⌊P G⌋" and
    B3:  "⌊P H⌋" *)


consts D :: "μ ⇒ σ" 
  
definition DL :: "μ ⇒ σ" where
  " DL (x) ≡ ❙¬(D(x))"  
    
definition Perfective1 ::  "(μ ⇒ σ) ⇒ σ" where 
    "  Perfective1 (φ)  ≡ ( (❙∀⇧Ex.( (❙¬ (φ(x))) □→  D(x) ) ))"  
    
definition Perfective2 ::  "(μ ⇒ σ) ⇒ σ" where 
    "  Perfective2 (φ)  ≡  ❙¬( ❙∃⇧Ex.( φ(x) □→ D(x) ))"      
  
definition Perfective ::  "(μ ⇒ σ) ⇒ σ" where 
    "  Perfective (φ)  ≡ ( (❙∀⇧Ex.( (❙¬ (φ(x))) □→  D(x) ) ))  ❙∧    ( ❙¬( ❙∃⇧Ex.( φ(x) □→ D(x) )))"

lemma PerfConj : "⌊Perfective(φ) ❙↔  (Perfective1(φ)  ❙∧ Perfective2(φ))⌋ "
  apply (metis Perfective_def Perfective1_def Perfective2_def)
  prf
  done

subsection ‹* Consistency *›

(*Proof found *)
lemma True 
  nitpick [satisfy, user_axioms, card i=2, expect = genuine] oops 
      
subsection ‹* HOL *›

(*Proof found,/nitpick failed *)
theorem Pred: "⌊❙∃Φ.( Φ x ❙↔  (❙∃⇧Ey. (x ❙=⇧L y) ))⌋"
  using nonempty by blast

(*Proof found,/nitpick failed *)    
theorem Taut: " True ❙⊢ p ⟹ ⌊❙∃Φ.( Φ ❙↔  p )⌋"
  using nonempty by blast
    
section ‹* Perfective- satisying A1 A2 *›    


(*Vampire found a proof- using Perfective_def nonempty by presburger *)
lemma A1CF: "⌊❙∀Φ. (((Perfective Φ) ❙→ ❙¬ (Perfective (⇧¬Φ)) )  )⌋"
  using Perfective1_def Perfective2_def PerfConj CF1 CF2 CF3 by metis

(*proof -
  have "sK0 ❙⊨ mexistsB eiw"
    by (simp add: nonempty)
  then have "(∃m. sK0 ❙⊨ (Perfective sK1 ❙∧ eiw m)) ∨ ⌊λi. ∀p. i ❙⊨ Perfective p ⟶ i ❙⊨ ❙¬ (Perfective (λm i. i ❙⊨ (⇧¬p) m))⌋"
    by metis (* > 1.0 s, timed out *)
  moreover
  { assume "∃m. sK0 ❙⊨ (Perfective sK1 ❙∧ eiw m)"
    then have ?thesis
      by (smt (z3) Perfective_def) (* > 1.0 s, timed out *) }
  ultimately show ?thesis
    by argo
qed *)


axiomatization where CF4: "∀w. {w} = Lew_Minset w (❙¬ ⊥)"

lemma A2CF1: "⌊❙∀Φ.( ❙∀Ψ.( ( (Perfective Φ) ❙∧ ❙□ (❙∀⇧Ex.( Φ x ❙→ Ψ x))) ❙→ Perfective1 Ψ))⌋"
  using  Perfective_def Perfective1_def CF1 CF2 CF3 CF4 by presburger
  (*nitpick[user_axioms] oops *)


lemma A2CF2: "⌊❙∀Φ.( ❙∀Ψ.( ( (Perfective Φ) ❙∧ ❙□ (❙∀⇧Ex.( Φ x ❙→ Ψ x))) ❙→   ❙¬(❙□(  ❙¬(Perfective2 Ψ) ))) )⌋"
  using Perfective_def Perfective2_def CF1 CF2 CF3 CF4 by metis

lemma A2CF23: "⌊❙∀Φ.( ❙∀Ψ.( ( (Perfective Φ) ❙∧ ❙□ (❙∀⇧Ex.( Φ x ❙→ Ψ x))) ❙→  (Perfective2 Ψ)) )⌋"
  using Perfective_def Perfective2_def CF1 CF2 CF3 CF4 by metis

        
lemma Giv2: "⌊Perfective2 DL⌋"
  using Perfective2_def DL_def CF3 CF1 by blast

lemma Giv1: "⌊Perfective1 DL⌋"
  using Perfective1_def DL_def CF3 CF1 by metis


(*Section:  Perfective V2*) 

consts OP :: "μ ⇒ σ"

definition DN :: "μ ⇒ σ" where
  " DN (x) ≡ ❙¬( (λy.  (❙□ ( OP(y)) ))(x)  )"
  
definition DNL :: "μ ⇒ σ" where
  " DNL (x) ≡ ❙¬(DN(x))"  
    
definition Pn1 ::  "(μ ⇒ σ) ⇒ σ" where 
    "  Pn1 (φ)  ≡ ( ❙□ (❙∀⇧Ex.( (❙¬ (φ(x))) ❙→  DN(x) ) ))"  
    
definition Pn2 ::  "(μ ⇒ σ) ⇒ σ" where 
    "  Pn2 (φ)  ≡  ❙¬ (❙□ (❙∀⇧Ex.( φ(x) ❙→  DN(x) )))"      
  
definition PerfectiveV2 ::  "(μ ⇒ σ) ⇒ σ" where 
    "  PerfectiveV2 (φ)  ≡ ( ❙□ (❙∀⇧Ex.( (❙¬ (φ(x))) ❙→  DN(x) ) ))  ❙∧   ❙¬ (❙□ (❙∀⇧Ex.( φ(x) ❙→  DN(x) )))"


lemma PN1Attempt2: "⌊PerfectiveV2(φ) ❙→ (Pn1 (λx. ❙□ (φ(x)) ))⌋"
nitpick [user_axioms, show_all] oops


lemma PN2Attempt2: "⌊PerfectiveV2(φ) ❙→ (Pn2 (λx. ❙□ (φ(x)) ))⌋"
 nitpick [user_axioms] oops



end
