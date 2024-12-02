theory QCFML
imports Main

begin
section {* QCML Attempt 1 *}

  typedecl i    (* "the type for possible worlds" *)
  typedecl j    (* "the type for elements of a set" *)
  typedecl \<mu>    (* "the type for individuals"  *)   

  consts r :: " i \<Rightarrow>(i \<Rightarrow> i \<Rightarrow> bool)"  (* "world ordering relations r_w"  *)

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
  
  consts IsIn_MinSet :: " i \<Rightarrow> (i \<Rightarrow> \<sigma>  \<Rightarrow> bool)" (* "x is in Min_w(phi)" *)

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
  
  abbreviation SetIs_Minset :: "bool"
  where "SetIs_Minset  \<equiv> (\<forall>w. \<forall>x. \<forall>\<Phi>. (IsIn_MinSet(w)(x)(\<Phi>) \<longleftrightarrow> (\<Phi> x) \<and> \<not>(\<exists>u.(r(w)(u)(x) \<and> u\<noteq>x))))"
  
  
  abbreviation mcbox :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<box>\<rightarrow>" 70) where "\<phi> \<box>\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)" 
  abbreviation mcdia :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>"  (infixr "\<diamond>\<rightarrow>" 70) where  "\<phi> \<diamond>\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)" 
  
  

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*)
    
(*Some metalogical Operators for Kripke frames*)    
abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") 
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation follows_w :: "i \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix"\<^bold>\<Turnstile>"55)
  where "(w  \<^bold>\<Turnstile> p)  \<equiv> p w  "
abbreviation follows_glob :: "bool \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix"\<^bold>\<turnstile>"40)
  where "(L \<^bold>\<turnstile> p )  \<equiv> (L \<longrightarrow> \<lfloor>p\<rfloor>)"
    
 (* Defining Min set*)

    
(*Some frequently used constraints for the accessibility relation*)    
abbreviation reflexive 
  where "reflexive \<equiv> (\<lambda>w. \<forall>x. r (w)(x)(x))"
abbreviation symmetric 
  where "symmetric \<equiv> (\<lambda>w. \<forall>x y. r (w)(x)(y) \<longrightarrow>  r (w)(y)(x))"
abbreviation serial :: "bool"
  where "serial \<equiv> (\<forall>x. \<exists>y. x  \<lambda>w. r w y)"
abbreviation transitive :: "bool"
  where "transitive \<equiv> (\<lambda>w. \<forall>x y z. ((w x r y) \<and> (w y r w) \<longrightarrow> (x  \<lambda>w. r w z)))"
abbreviation euclidean :: "bool"
  where "euclidean \<equiv> (\<forall>x y z. ((x  \<lambda>w. r w y) \<and> (x  \<lambda>w. r w z) \<longrightarrow> (y  \<lambda>w. r w z)))"
abbreviation irreflexive :: "bool"
  where  "irreflexive \<equiv>\<forall>x.  \<not>(x  \<lambda>w. r w x)"
abbreviation converselyWellFoundedser :: "bool"
  where "converselyWellFoundedser  \<equiv> ( \<not> (\<exists>f::(nat \<Rightarrow>  i).(\<forall>n::nat.(f(n)  \<lambda>w. r w f(Suc(n)))) ))"
abbreviation converselyWellFoundedset :: "bool"
  where "converselyWellFoundedset  \<equiv> \<forall>S::i\<Rightarrow>bool. (\<exists>a.(S(a)))  \<longrightarrow>  (\<exists>m.(S(m)  \<and> (\<forall>s.(S(s)   \<longrightarrow> (\<not> (m  \<lambda>w. r w s))  ))))  " 
abbreviation finiteWorlds :: "bool"
  where "finiteWorlds \<equiv> finite (UNIV :: i set)"
    
(*Some common modal logics*)
abbreviation K4_sem :: bool
 where "K4_sem  \<equiv> transitive"
abbreviation S4_sem :: bool
 where "S4_sem  \<equiv> reflexive \<and> transitive"
abbreviation S5_sem :: bool 
 where "S5_sem  \<equiv> reflexive \<and> euclidean"
abbreviation GL_sem_ser :: bool
  where "GL_sem_ser  \<equiv> converselyWellFoundedser \<and> transitive"
abbreviation GL_sem_set :: bool
  where "GL_sem_set  \<equiv> converselyWellFoundedset \<and> transitive"
abbreviation GL_sem_fin ::bool
  where "GL_sem_fin \<equiv> transitive \<and> irreflexive \<and> finiteWorlds"

end