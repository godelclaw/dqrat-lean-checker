import DqratLean.DependencyRemovalContinuation

/-!
\begin{lemma}[Dependency Removal]
                Suppose we have a DQBF $\Pi\exists x(D_x) \phi$.
                $\Pi$ contains a list of quantified universal variables $U$ and a list
of existential variables $E$ with Henkin quantifiers, each existential
variable $e$ is paired with a dependency set $D_e$ a subset of $U$.
$D_x$ is the dependency set of of $x$ and is also  subset of $U$.
                $\phi$ is the propositional matrix written as a conjunctive normal
form using only variables from $U$ and $E$ and $x$.

                Suppose there is some $u \in D_x$, and none of these conditions are
satisfied
                \begin{itemize}
                        \item a $u$-pure path from $u$ to $l$ and a $\bar u $-pure path from
$\bar u $ to $\bar l$
                        \item a  $u$-pure path from $u$ to $\bar l$ and a $\bar u $-path from
$\bar u $ to $l$
                \end{itemize}
                Then if $\Pi\exists x(D_x) \phi$ is satisfiable then so is $\Pi\exists
x(D_x\setminus\{u\}) \phi$.

        \end{lemma}

        \begin{proof}
                Let $f=\{ f_e \mid e\in E\}$ be a set of Skolem functions that
satisfies $\Pi\exists x(D_x) \phi$.
                We will construct a set of Skolem functions $f^*=\{ f^*_e \mid e\in
E\}$ that satisfies $\Pi\exists x(D_x\setminus\{u\}) \phi$.
-/

/-!
                We use the following definitions:
                \begin{itemize}
                \item If $\alpha$ is partial assignment to the universal variables,
$\alpha^v$ is obtained by flipping the Boolean value of universal
variable $v$.
                % definition
                \item Given $f$ a \emph{dependency witness} is a  triple $(\alpha, y,
v)$ where $f_y(\alpha)\neq  f_y(\alpha^v)$, $y$ is an existential
variable, $v$ is a universal variable, $\alpha$ is an assignment to
$D_y$
                %\item The \textit{hairiness} $h(f)$ of Skolem set $f$ is the number
of triples $(\alpha, y, v)$ for which $f_y(\alpha)\neq  f_y(\alpha^v)$
                \item The set $\mathcal{S}_u=\{z:u \in D_z\}$
                \item For universal literal $l$: $\phi_l= \{C \in \phi \mid l\in C\}$.
                \item For an existential variable $z$, and assignment $\gamma\in
\{0,1\}^U$: $\gamma_z= \gamma|_{D_{z}}$
                \end{itemize}
-/

theorem dependencyWitnessCount_zero_iff_independent
    {f : DQBF} {vars : Array Var} {on_ : Var} {sk : SkolemAssignment}
    (hexi : ∀ of_ ∈ vars.toList, f.isVarExistential of_ = true) :
    deleteWitnessFiberCountSet f vars on_ sk = 0 ↔
      ExhibitsDeleteIndependenceSet f vars on_ sk :=
  deleteWitnessFiberCountSet_zero_iff_exhibits f vars on_ sk hexi

theorem dependencyWitnessCount_nonzero_iff_exists_witness
    {f : DQBF} {vars : Array Var} {on_ : Var} {sk : SkolemAssignment} :
    deleteWitnessFiberCountSet f vars on_ sk ≠ 0 ↔
      ∃ of_, of_ ∈ vars.toList ∧ ∃ σ,
        DeleteDepWitness f of_ on_ sk σ :=
  deleteWitnessFiberCountSet_ne_zero_iff_existsDeleteDepWitness f vars on_ sk

/-!
                Suppose $f$ has a dependency witness $(\alpha, x, u)$ where $u \in
\mathrm{D}_x^\Pi \setminus \mathrm{D}_x^{\Pi'}$.
                Let $l_u$ be the literal on $u$ satisfied by $\alpha$, $l_x$ the
literal on $x$ satisfied by $f_x(\alpha)$.
                Since $u \not \in \mathrm{D}_x^{\Pi'}$, by definition either $\bar l_u
\not\pusim l_x$ or $l_u \not\pusim \bar l_x$.
                Without loss of generality, let $\bar l_u \not\pusim l_x$ (in the
other case, swap the roles of $\alpha$ and $\alpha^u$).
-/

/-!
                Define $\mpool = \mpool(f, \bar l_u, l_x, \alpha)$ as the set of all
Skolem sets $f'=\{f'_x \mid  x\in E\}$ respecting the prefix $\Pi$ with
the following properties:
                \begin{enumerate}
                        \item The set of dependency witnesses in $f'$ and $u$ are a
\emph{proper} subset of dependency witness in $f$ and $u$. i.e if $f'$
has a dependency witness $(\delta, y,u)$ then $f$ has dependency witness
$(\delta, y,u)$ and there is least one dependency witness for $f$ that
is not present for $f'$.
                        \label{item:hairiness}
                        \item For every existential variable $z$, for every
                        $ \gamma \in \{0,1\}^{D(z)}$, if
                         $f'_z (\gamma_z) \neq f_z(\gamma_z)$  then $\gamma_z$ satisfies
$l_u$; i.e. $u\in D(z)$ and $l_u$'s polarity matches with $\gamma_z$.

                        \label{item:assignment}
                        \item For every existential variable $z$, for every $\gamma \in
\{0,1\}^{D(z)}$, if
                        $f'_z (\gamma_z) \neq f_z(\gamma_z)$  then
                        for the literal $l_z$ satisfied by $f_z(\gamma_z)$,
                        $\bar l_u \not \pusim l_z$.
                \end{enumerate}
-/

/-!
                We first show that $\mpool$ is non-empty. Let
%               Let $f^0=\{f^0_y \mid y \in \var_\exists(\Pi)\}$ so that $f^0_y =
f_y$ for all $y \neq x$ and $f^0_x(\tau)$ agrees with $f_x (\tau)  $,
unless $\tau=\alpha$ in which case $f^0_x(\tau)=\neg f_x(\tau)$.
                        \[ f^0=\{f^0_z \mid z \in E \}\quad
                                f^0_z(\tau) = \begin{cases}
                                                \neg f_x(\tau) & \text{ if } \tau = \alpha \text{ and } z=x\\
                                                f_z (\tau)     & \text{ otherwise,}
                                        \end{cases}
                        \]
                        %and , i.e.,
                        %flip the value of $f^0_x$ for $\alpha$.
                \begin{enumerate}
                \item
                $f^0$ satisfies property~%\ref{item:harmony},
                \ref{item:hairiness} because $(\alpha, x, u)$ and $(\alpha^u, x, u)$
are dependency witnesses that are removed.
                For any dependency witness $(\delta, w, u)$ present in $f^0$ then
$w\neq x$ or ($\delta\neq \alpha$ and $\delta\neq \alpha^u$ ) and so
$f^0_w(\delta)=f_w(\delta)$ and $f^0_w(\delta^u)=f_w(\delta^u)$ so
$(\delta, w, u)$ is a dependency witness in $f$.
                \item $f^0$ only differs from $f$ on $\alpha$ and its extensions, but
$\alpha$ satisfies $l_u$.
                \item $f_z^0$ only differs from $f_z$ when $z=x$ however we have
assumed that $\bar l_u \not \pusim l_x$ and $f_x(\alpha)$ satisfies
$l_x$.
                \end{enumerate}
-/

theorem dependencyRemoval_initialPatch_reducesWitnessFiberCount
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {sk : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ sk σSeed) :
    deleteWitnessFiberCountSet s.formula vars on_
        (patchDeleteWitnessAt s.formula of_ σSeed sk) <
      deleteWitnessFiberCountSet s.formula vars on_ sk :=
  deleteWitnessFiberCountSet_patchDeleteWitnessAt_lt_of_mem
    s.formula vars of_ on_ σSeed sk hof (hexi of_ hof)
    (hcontains of_ hof) hwit

theorem dependencyRemoval_initialPatch_inRepairPool
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {sk : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ sk σSeed)
    (hnoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit of_ (s.formula.varValue σSeed sk of_))) :
    FlexibleRepairPoolTracked s vars on_ sk
      (patchDeleteWitnessAt s.formula of_ σSeed sk) := by
  refine ⟨?_, ?_, ?_⟩
  · exact flexibleRepairPoolCandidate_of_patchPoolCandidate
      (patchPoolCandidate_initial_patch
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σSeed := σSeed)
        hexi hcontains hof hwit hnoPath)
  · exact flexibleRepairPoolFiberFootprint_initial_patch
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (sk := sk) (σSeed := σSeed) hexi hof hwit
  · exact flexibleRepairPoolLiveWitnessFiberUnchanged_initial_patch
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (sk := sk) (σSeed := σSeed) hexi hcontains hof hwit

/-!
                Next we will define the inductive step. We show that if $f'\in \mpool$
is not a model then there is $f''\in \mpool$ where the dependency
witnesses of $f''$ and $u$ are a proper subset of the dependency
witnesses of $f'$.

                First we need to construct such a $f''$. We know that if $f'$ is not a
model of $\Pi\exists x(D_x) \phi$, then there is some assignment
$\gamma\in \{0,1\}^{E}$ and some clause $C\in \phi$ such that the
assignment $\gamma \cup f'(\gamma)$ falsifies $C$.
                However we know that $\gamma \cup f(\gamma)$ satisfies $C$ because $f$
is a model. Hence there is some existential variable $z$ such that
$f'_z(\gamma_z)\neq f_z(\gamma_z)$ and some literal $l_z$ in $z$ such
that $f_z(\gamma_z)$ satisfies $l_z$ and $f'_z(\gamma_z)$ falsifies
$l_z$. By property~\ref{item:assignment}: $ \gamma_z$ satisfies $l_u$,
and by property~\ref{item:path}: $\bar l_u \not \pusim l_z$.
-/

theorem dependencyRemoval_poolCandidate_model_or_counterexample
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment}
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand) :
    (∃ sk',
      (∀ σ, s.clauses.matrixValue s.formula σ sk' = true) ∧
      deleteWitnessFiberCountSet s.formula vars on_ sk' <
        deleteWitnessFiberCountSet s.formula vars on_ skBase) ∨
    ∃ σ, s.clauses.matrixValue s.formula σ skCand = false := by
  classical
  by_cases hfail :
      ∃ σ, s.clauses.matrixValue s.formula σ skCand = false
  · exact Or.inr hfail
  · left
    refine ⟨skCand, ?_, hpool.1⟩
    intro σ
    cases hval : s.clauses.matrixValue s.formula σ skCand with
    | false => exact False.elim (hfail ⟨σ, hval⟩)
    | true => rfl

theorem dependencyRemoval_matrixValue_false_of_false_clause
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment)
    (sk : SkolemAssignment) {cref : CRef} {c : Clause}
    (hget : cs.getClause cref = some c)
    (hfalse : f.clauseValue σ sk c.lits = false) :
    cs.matrixValue f σ sk = false := by
  cases hmat : cs.matrixValue f σ sk with
  | false => rfl
  | true =>
      have htrue : f.clauseValue σ sk c.lits = true :=
        clauseValue_of_matrixValue f cs σ sk cref c hmat hget
      rw [hfalse] at htrue
      cases htrue

theorem dependencyRemoval_clauseValue_false_implies_lit_false
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (lits : Array Literal)
    (hfalse : f.clauseValue σ sk lits = false) :
    ∀ l ∈ lits.toList, f.litValue σ sk l = false := by
  intro l hl
  rcases Bool.eq_false_or_eq_true (f.litValue σ sk l) with hl_true | hl_false
  · exfalso
    have hmem : l ∈ lits := Array.mem_toList_iff.mp hl
    rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi, rfl⟩
    have hclauseTrue : f.clauseValue σ sk lits = true := by
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨i, hi, hl_true⟩
    rw [hclauseTrue] at hfalse
    cases hfalse
  · exact hl_false

theorem dependencyRemoval_clauseValue_true_of_mem_lit_true
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    {lits : Array Literal} {lit : Literal}
    (hmem : lit ∈ lits.toList)
    (htrue : f.litValue σ sk lit = true) :
    f.clauseValue σ sk lits = true := by
  have harrayMem : lit ∈ lits := Array.mem_toList_iff.mp hmem
  rcases Array.mem_iff_getElem.mp harrayMem with ⟨i, hi, hget⟩
  simp only [DQBF.clauseValue, Array.any_eq_true]
  exact ⟨i, hi, by simpa [hget] using htrue⟩

theorem dependencyRemoval_litValue_true_false_varValue_ne
    (f : DQBF) (σ : UnivAssignment)
    (skTrue skFalse : SkolemAssignment) (l : Literal)
    (htrue : f.litValue σ skTrue l = true)
    (hfalse : f.litValue σ skFalse l = false) :
    f.varValue σ skFalse l.var ≠ f.varValue σ skTrue l.var := by
  unfold DQBF.litValue at htrue hfalse
  by_cases hpos : l.isPos
  · simp [hpos] at htrue hfalse
    rw [htrue, hfalse]
    simp
  · simp [hpos] at htrue hfalse
    cases hbase : f.varValue σ skTrue l.var <;>
      cases hcand : f.varValue σ skFalse l.var <;>
      simp [hbase, hcand] at htrue hfalse ⊢

theorem dependencyRemoval_falsifiedClause_changedLiteral
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    ∃ cref c l,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue σ skCand c.lits = false ∧
      l ∈ c.lits.toList ∧
      l.var ∈ vars.toList ∧
      s.formula.litValue σ skBase l = true ∧
      s.formula.litValue σ skCand l = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) l := by
  rcases matrixValue_false_implies_exists_false_clause
      s.formula s.clauses σ skCand hfalse with
    ⟨cref, c, hget, hclauseFalse⟩
  have hclauseTrue :
      s.formula.clauseValue σ skBase c.lits = true :=
    clauseValue_of_matrixValue s.formula s.clauses σ skBase cref c
      (hallBase σ) hget
  rcases clauseValue_true_false_implies_exists_true_false_lit
      s.formula σ skBase skCand c.lits hclauseTrue hclauseFalse with
    ⟨l, hlmem, hltrue, hlfalse⟩
  have hdiff :
      s.formula.varValue σ skCand l.var ≠
        s.formula.varValue σ skBase l.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand l hltrue hlfalse
  rcases hpool.2.2 l.var σ hdiff with ⟨hmem, hnoPath⟩
  have hlEq :
      l = mkLit l.var (s.formula.varValue σ skBase l.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula l.var σ skBase l rfl hltrue
  have hnoPathLit :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) l := by
    rw [hlEq]
    exact hnoPath
  exact ⟨cref, c, l, hget, hclauseFalse, hlmem, hmem, hltrue,
    hlfalse, hnoPathLit⟩

/-!
                On $\gamma^u$, we have that $l_u$ is falsified so $f'$ and $f$ are
equal by property~\ref{item:assignment}.  This means that
$f'_z(\gamma^u_z)=f_z(\gamma^u_z)$. Therefore if $f_z(\gamma_z)\neq
f_z(\gamma^u_z)$ (i.e. $(\gamma_z, z, u)$ is not a dependency witness in
$f$) then
                $f'_z(\gamma_z)\neq f_z(\gamma_z)=f_z(\gamma^u_z)=f'_z(\gamma^u_z)$
(i.e. $(\gamma_z, z, u)$ is a dependency witness in $f'$) violating
property~\ref{item:hairiness}, so $f_z(\gamma^u_z)\neq f_z(\gamma^u_z)$
and $f'_z(\gamma_z)=f'_z(\gamma^u_z)$.
-/

theorem dependencyRemoval_changedValue_baseWitnessAndNoPath
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hdiff :
      s.formula.varValue σ skCand of_ ≠
        s.formula.varValue σ skBase of_) :
    of_ ∈ vars.toList ∧
      DeleteDepWitness s.formula of_ on_ skBase σ ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit of_ (s.formula.varValue σ skBase of_)) := by
  rcases htracked with ⟨hpool, hfoot, _hlive⟩
  rcases hfoot of_ σ hdiff with ⟨hof, hwitBase, _hfiber⟩
  rcases hpool.2.2 of_ σ hdiff with ⟨_hof, hnoPath⟩
  exact ⟨hof, hwitBase, hnoPath⟩

theorem dependencyRemoval_liveCandidateWitness_agreesWithBase
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hof : of_ ∈ vars.toList)
    (hwitCand : DeleteDepWitness s.formula of_ on_ skCand σ) :
    s.formula.varValue σ skCand of_ =
        s.formula.varValue σ skBase of_ ∧
      s.formula.varValue (flipUniv on_ σ) skCand of_ =
        s.formula.varValue (flipUniv on_ σ) skBase of_ := by
  constructor
  · exact htracked.2.2 of_ σ σ hof hwitCand rfl
  · exact htracked.2.2 of_ σ (flipUniv on_ σ) hof hwitCand
      (deleteDepArgs_flipUniv s.formula of_ on_ σ)

theorem dependencyRemoval_deleteDepWitness_flipUniv_iff
    (f : DQBF) (of_ on_ : Var) (sk : SkolemAssignment)
    (σ : UnivAssignment) :
    DeleteDepWitness f of_ on_ sk (flipUniv on_ σ) ↔
      DeleteDepWitness f of_ on_ sk σ := by
  unfold DeleteDepWitness
  have hflip : flipUniv on_ (flipUniv on_ σ) = σ := by
    funext v
    by_cases hv : v = on_
    · subst v
      simp [flipUniv]
    · simp [flipUniv, hv]
  rw [hflip]
  constructor <;> intro hneq
  · exact Ne.symm hneq
  · exact Ne.symm hneq

/-!
The TeX proof uses the following Boolean fact when it says that, on
\(\gamma^u\), the current Skolem functions and the original Skolem functions
agree.  If the original has a dependency witness, the current candidate differs
from the original on one side, and that witness is absent from the current
candidate, then the current candidate must agree with the original on the
flipped side.
-/

theorem dependencyRemoval_removedChangedBaseWitness_flipSide_agreesWithBase
    (f : DQBF) (of_ on_ : Var)
    (skBase skCand : SkolemAssignment) (σ : UnivAssignment)
    (hbase : DeleteDepWitness f of_ on_ skBase σ)
    (hnotCand : ¬ DeleteDepWitness f of_ on_ skCand σ)
    (hchanged :
      f.varValue σ skCand of_ ≠ f.varValue σ skBase of_) :
    f.varValue (flipUniv on_ σ) skCand of_ =
      f.varValue (flipUniv on_ σ) skBase of_ := by
  unfold DeleteDepWitness at hbase hnotCand
  cases hbaseσ : f.varValue σ skBase of_ <;>
    cases hbaseFlip : f.varValue (flipUniv on_ σ) skBase of_ <;>
    cases hcandσ : f.varValue σ skCand of_ <;>
    cases hcandFlip : f.varValue (flipUniv on_ σ) skCand of_ <;>
    simp_all

theorem dependencyRemoval_removedBaseWitness_sideSplit_opposite_agrees
    (f : DQBF) (of_ on_ : Var)
    (skBase skCand : SkolemAssignment) (τ σSide : UnivAssignment)
    (hbase : DeleteDepWitness f of_ on_ skBase τ)
    (hnotCand : ¬ DeleteDepWitness f of_ on_ skCand τ)
    (hside : σSide = τ ∨ σSide = flipUniv on_ τ)
    (hchanged :
      f.varValue σSide skCand of_ ≠
        f.varValue σSide skBase of_) :
    (σSide = τ ∧
        f.varValue (flipUniv on_ τ) skCand of_ =
          f.varValue (flipUniv on_ τ) skBase of_) ∨
      (σSide = flipUniv on_ τ ∧
        f.varValue τ skCand of_ =
          f.varValue τ skBase of_) := by
  rcases hside with hside | hside
  · subst σSide
    exact Or.inl
      ⟨rfl,
        dependencyRemoval_removedChangedBaseWitness_flipSide_agreesWithBase
          f of_ on_ skBase skCand τ hbase hnotCand hchanged⟩
  · subst σSide
    have hbaseFlip :
        DeleteDepWitness f of_ on_ skBase (flipUniv on_ τ) :=
      (dependencyRemoval_deleteDepWitness_flipUniv_iff
        f of_ on_ skBase τ).2 hbase
    have hnotCandFlip :
        ¬ DeleteDepWitness f of_ on_ skCand (flipUniv on_ τ) := by
      intro hwitFlip
      exact hnotCand
        ((dependencyRemoval_deleteDepWitness_flipUniv_iff
          f of_ on_ skCand τ).1 hwitFlip)
    have hagree :
        f.varValue (flipUniv on_ (flipUniv on_ τ)) skCand of_ =
          f.varValue (flipUniv on_ (flipUniv on_ τ)) skBase of_ :=
      dependencyRemoval_removedChangedBaseWitness_flipSide_agreesWithBase
        f of_ on_ skBase skCand (flipUniv on_ τ)
        hbaseFlip hnotCandFlip hchanged
    have hflip_involutive : flipUniv on_ (flipUniv on_ τ) = τ := by
      funext v
      by_cases hv : v = on_
      · subst v
        simp [flipUniv]
      · simp [flipUniv, hv]
    exact Or.inr ⟨rfl, by simpa [hflip_involutive] using hagree⟩

theorem dependencyRemoval_litValue_mkLit_true
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) :
    f.litValue σ sk (mkLit v true) = f.varValue σ sk v := by
  unfold DQBF.litValue
  rw [mkLit_var_early]
  simp [Literal.isPos, mkLit]

theorem dependencyRemoval_litValue_mkLit_false
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) :
    f.litValue σ sk (mkLit v false) = !(f.varValue σ sk v) := by
  unfold DQBF.litValue
  rw [mkLit_var_early]
  simp [Literal.isPos, mkLit]

theorem dependencyRemoval_litValue_mkLit_universal_sigma_true
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (huniv : f.isVarExistential on_ = false) :
    f.litValue σ sk (mkLit on_ (σ on_)) = true := by
  cases hσ : σ on_
  · rw [dependencyRemoval_litValue_mkLit_false]
    simp [DQBF.varValue, huniv, hσ]
  · rw [dependencyRemoval_litValue_mkLit_true]
    simp [DQBF.varValue, huniv, hσ]

theorem dependencyRemoval_litValue_flipUniv_mkLit_universal_not_sigma_true
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (huniv : f.isVarExistential on_ = false) :
    f.litValue (flipUniv on_ σ) sk (mkLit on_ (!(σ on_))) = true := by
  simpa [flipUniv] using
    dependencyRemoval_litValue_mkLit_universal_sigma_true
      f on_ (flipUniv on_ σ) sk huniv

theorem dependencyRemoval_removedChangedBaseWitness_oldLiteralFalseOnFlip
    (f : DQBF) (of_ on_ : Var)
    (skBase skCand : SkolemAssignment) (σ : UnivAssignment)
    (hbase : DeleteDepWitness f of_ on_ skBase σ)
    (hnotCand : ¬ DeleteDepWitness f of_ on_ skCand σ)
    (hchanged :
      f.varValue σ skCand of_ ≠ f.varValue σ skBase of_) :
    f.litValue (flipUniv on_ σ) skCand
        (mkLit of_ (f.varValue σ skBase of_)) = false := by
  have hagreeFlip :
      f.varValue (flipUniv on_ σ) skCand of_ =
        f.varValue (flipUniv on_ σ) skBase of_ :=
    dependencyRemoval_removedChangedBaseWitness_flipSide_agreesWithBase
      f of_ on_ skBase skCand σ hbase hnotCand hchanged
  cases hbaseσ : f.varValue σ skBase of_
  · have hbaseFlip :
        f.varValue (flipUniv on_ σ) skBase of_ = true := by
      unfold DeleteDepWitness at hbase
      cases hflip : f.varValue (flipUniv on_ σ) skBase of_ <;>
        simp_all
    rw [dependencyRemoval_litValue_mkLit_false, hagreeFlip, hbaseFlip]
    simp
  · have hbaseFlip :
        f.varValue (flipUniv on_ σ) skBase of_ = false := by
      unfold DeleteDepWitness at hbase
      cases hflip : f.varValue (flipUniv on_ σ) skBase of_ <;>
        simp_all
    rw [dependencyRemoval_litValue_mkLit_true, hagreeFlip, hbaseFlip]

/-!
When the residual proof finds another patch footprint, it is not only a
changed value.  Because the candidate is still in the repair pool, the same
footprint carries the TeX proof's path side condition: there is no pure path
from the opposite \(u\)-literal to the original literal for that changed value.
-/

theorem dependencyRemoval_currentResidualPatchFootprint_noPurePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hpatch :
      DependencyRemovalCurrentResidualPatchFootprint
        s vars on_ skBase skCand skNext σ) :
    ∃ patched τ σSide,
      patched ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula patched on_ skCand τ ∧
      DeleteDepWitness s.formula patched on_ skBase τ ∧
      (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
      DeleteDepWitness s.formula patched on_ skBase σSide ∧
      s.formula.varValue σSide skCand patched ≠
        s.formula.varValue σSide skBase patched ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
        (mkLit patched (s.formula.varValue σSide skBase patched)) ∧
      ∀ ρ,
        deleteDepArgs s.formula patched on_ ρ =
          deleteDepArgs s.formula patched on_ σSide →
        s.formula.varValue ρ skCand patched ≠
          s.formula.varValue ρ skBase patched →
        fullDepArgs s.formula patched ρ =
          fullDepArgs s.formula patched σSide := by
  rcases hpatch with
    ⟨patched, τ, σSide, hof, hnotCand, hbaseτ, hside, hbaseSide,
      hchanged, hfiber⟩
  rcases dependencyRemoval_changedValue_baseWitnessAndNoPath
      (s := s) (vars := vars) (on_ := on_) (of_ := patched)
      (skBase := skBase) (skCand := skCand) (σ := σSide)
      htracked hchanged with
    ⟨_hof, _hbaseSide, hnoPath⟩
  exact ⟨patched, τ, σSide, hof, hnotCand, hbaseτ, hside,
    hbaseSide, hchanged, hnoPath, hfiber⟩

/-!
The preceding agreement statement is exactly what the TeX proof uses to say
that the old literal is false on the flipped assignment.  The next lemma keeps
that as a single auditable package: a residual patch footprint gives the
changed side, the no-pure-path side condition for the old literal, and the
fact that the old literal is false after flipping \(u\).
-/

theorem dependencyRemoval_currentResidualPatchFootprint_flipObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hpatch :
      DependencyRemovalCurrentResidualPatchFootprint
        s vars on_ skBase skCand skNext σ) :
    ∃ patched τ σSide,
      patched ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula patched on_ skCand τ ∧
      DeleteDepWitness s.formula patched on_ skBase τ ∧
      (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
      DeleteDepWitness s.formula patched on_ skBase σSide ∧
      s.formula.varValue σSide skCand patched ≠
        s.formula.varValue σSide skBase patched ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
        (mkLit patched (s.formula.varValue σSide skBase patched)) ∧
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit patched (s.formula.varValue σSide skBase patched)) =
          false ∧
      ∀ ρ,
        deleteDepArgs s.formula patched on_ ρ =
          deleteDepArgs s.formula patched on_ σSide →
        s.formula.varValue ρ skCand patched ≠
          s.formula.varValue ρ skBase patched →
        fullDepArgs s.formula patched ρ =
          fullDepArgs s.formula patched σSide := by
  rcases dependencyRemoval_currentResidualPatchFootprint_noPurePath
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      htracked hpatch with
    ⟨patched, τ, σSide, hof, hnotCand, hbaseτ, hside,
      hbaseSide, hchanged, hnoPath, hfiber⟩
  have hnotSide :
      ¬ DeleteDepWitness s.formula patched on_ skCand σSide := by
    rcases hside with hside | hside
    · simpa [hside] using hnotCand
    · intro hwitSide
      have hwitτ :
          DeleteDepWitness s.formula patched on_ skCand τ := by
        exact
          (dependencyRemoval_deleteDepWitness_flipUniv_iff
            s.formula patched on_ skCand τ).1 (by
              simpa [hside] using hwitSide)
      exact hnotCand hwitτ
  have holdFalse :
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit patched (s.formula.varValue σSide skBase patched)) =
          false :=
    dependencyRemoval_removedChangedBaseWitness_oldLiteralFalseOnFlip
      s.formula patched on_ skBase skCand σSide
      hbaseSide hnotSide hchanged
  exact ⟨patched, τ, σSide, hof, hnotCand, hbaseτ, hside,
    hbaseSide, hchanged, hnoPath, holdFalse, hfiber⟩

/-!
The shared current frontier packages exactly the residual false-clause data
that the TeX proof uses next.  From it, Lean recovers the old literal whose
current value differs from the original satisfying Skolem functions, the
missing pure path to that old literal, and the fact that the old literal is
false after flipping \(u\).
-/

theorem dependencyRemoval_currentFrontier_flipObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hcurrent :
      DependencyRemovalCurrentResidualFrontier
        s vars on_ skBase skCand skNext σ) :
    ∃ patched τ σSide,
      patched ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula patched on_ skCand τ ∧
      DeleteDepWitness s.formula patched on_ skBase τ ∧
      (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
      DeleteDepWitness s.formula patched on_ skBase σSide ∧
      s.formula.varValue σSide skCand patched ≠
        s.formula.varValue σSide skBase patched ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
        (mkLit patched (s.formula.varValue σSide skBase patched)) ∧
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit patched (s.formula.varValue σSide skBase patched)) =
          false ∧
      ∀ ρ,
        deleteDepArgs s.formula patched on_ ρ =
          deleteDepArgs s.formula patched on_ σSide →
        s.formula.varValue ρ skCand patched ≠
          s.formula.varValue ρ skBase patched →
        fullDepArgs s.formula patched ρ =
          fullDepArgs s.formula patched σSide :=
  dependencyRemoval_currentResidualPatchFootprint_flipObservation
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    htracked
    (dependencyRemoval_currentResidual_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hcurrent)

/-!
The residual branch also needs the exact false clause, not only the fact that
some patch fiber changed.  The next three Lean lemmas keep that data visible:
if a two-patch Skolem set falsifies the matrix, then a false clause contains a
literal whose truth changed because of one of the two patches.
-/

theorem dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
    (f : DQBF) (of_ : Var) (σ₀ τ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (hne : l.var ≠ of_) :
    f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l =
      f.litValue τ sk l := by
  unfold DQBF.litValue
  rw [varValue_patchDeleteWitnessAt_eq_of_ne f of_ σ₀ τ sk hne]

theorem dependencyRemoval_litValue_twoPatch_eq_of_ne_vars
    (f : DQBF) (of_ nextOf : Var)
    (σ₀ σ τ : UnivAssignment) (sk : SkolemAssignment) (l : Literal)
    (hneOf : l.var ≠ of_) (hneNext : l.var ≠ nextOf) :
    f.litValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) l =
      f.litValue τ sk l := by
  rw [dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
      f nextOf σ τ (patchDeleteWitnessAt f of_ σ₀ sk) l hneNext,
    dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
      f of_ σ₀ τ sk l hneOf]

theorem dependencyRemoval_matrixValue_twoPatch_false_changedClause
    (f : DQBF) (cs : ClauseStore) (of_ nextOf : Var)
    (σ₀ σ τ : UnivAssignment) (sk : SkolemAssignment)
    (hall : ∀ ρ, cs.matrixValue f ρ sk = true)
    (hfalse :
      cs.matrixValue f τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) = false) :
    ∃ cref c l,
      cs.getClause cref = some c ∧
      f.clauseValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) c.lits = false ∧
      l ∈ c.lits.toList ∧
      (l.var = of_ ∨ l.var = nextOf) ∧
      f.litValue τ sk l = true ∧
      f.litValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) l = false := by
  rcases matrixValue_false_implies_exists_false_clause
      f cs τ
      (patchDeleteWitnessAt f nextOf σ
        (patchDeleteWitnessAt f of_ σ₀ sk)) hfalse with
    ⟨cref, c, hget, hclauseFalse⟩
  have hclauseTrue : f.clauseValue τ sk c.lits = true :=
    clauseValue_of_matrixValue f cs τ sk cref c (hall τ) hget
  rcases clauseValue_true_false_implies_exists_true_false_lit
      f τ sk
      (patchDeleteWitnessAt f nextOf σ
        (patchDeleteWitnessAt f of_ σ₀ sk)) c.lits
      hclauseTrue hclauseFalse with
    ⟨l, hlmem, hltrue, hlfalse⟩
  have hvar : l.var = of_ ∨ l.var = nextOf := by
    by_cases hEqOf : l.var = of_
    · exact Or.inl hEqOf
    · by_cases hEqNext : l.var = nextOf
      · exact Or.inr hEqNext
      · have hsame :
          f.litValue τ
              (patchDeleteWitnessAt f nextOf σ
                (patchDeleteWitnessAt f of_ σ₀ sk)) l =
            f.litValue τ sk l :=
          dependencyRemoval_litValue_twoPatch_eq_of_ne_vars
            f of_ nextOf σ₀ σ τ sk l hEqOf hEqNext
        rw [hsame, hltrue] at hlfalse
        cases hlfalse
  exact ⟨cref, c, l, hget, hclauseFalse, hlmem, hvar, hltrue,
    hlfalse⟩

theorem dependencyRemoval_twoPatch_changedClause_cases
    (f : DQBF) (cs : ClauseStore) {of_ nextOf on_ : Var}
    {σ₀ σ τ : UnivAssignment} {sk : SkolemAssignment}
    (hnextNe : nextOf ≠ of_)
    (hexiOf : f.isVarExistential of_ = true)
    (hcontainsOf : (f.depset.getD of_ #[]).contains on_ = true)
    (hexiNext : f.isVarExistential nextOf = true)
    (hcontainsNext : (f.depset.getD nextOf #[]).contains on_ = true)
    (hchanged :
      ∃ cref c l,
        cs.getClause cref = some c ∧
        f.clauseValue τ
          (patchDeleteWitnessAt f nextOf σ
            (patchDeleteWitnessAt f of_ σ₀ sk)) c.lits = false ∧
        l ∈ c.lits.toList ∧
        (l.var = of_ ∨ l.var = nextOf) ∧
        f.litValue τ sk l = true ∧
        f.litValue τ
          (patchDeleteWitnessAt f nextOf σ
            (patchDeleteWitnessAt f of_ σ₀ sk)) l = false) :
    (∃ cref c l,
      cs.getClause cref = some c ∧
      f.clauseValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) c.lits = false ∧
      l ∈ c.lits.toList ∧
      l.var = of_ ∧
      f.litValue τ sk l = true ∧
      f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l = false ∧
      PatchChangedFiber f cs of_ on_ σ₀ τ sk) ∨
    (∃ cref c l,
      cs.getClause cref = some c ∧
      f.clauseValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) c.lits = false ∧
      l ∈ c.lits.toList ∧
      l.var = nextOf ∧
      f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l = true ∧
      f.litValue τ
        (patchDeleteWitnessAt f nextOf σ
          (patchDeleteWitnessAt f of_ σ₀ sk)) l = false ∧
      PatchChangedFiber f cs nextOf on_ σ τ
        (patchDeleteWitnessAt f of_ σ₀ sk)) := by
  rcases hchanged with
    ⟨cref, c, l, hget, hclauseFalse, hlmem, hvar, hltrue,
      hlfalse⟩
  rcases hvar with hvarOf | hvarNext
  · left
    have hneNext : l.var ≠ nextOf := by
      intro hEq
      exact hnextNe (hEq.symm.trans hvarOf)
    have hfalseFirst :
        f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l = false := by
      have hsame :
          f.litValue τ
              (patchDeleteWitnessAt f nextOf σ
                (patchDeleteWitnessAt f of_ σ₀ sk)) l =
            f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l :=
        dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
          f nextOf σ τ (patchDeleteWitnessAt f of_ σ₀ sk) l hneNext
      rw [hsame] at hlfalse
      exact hlfalse
    have hchangedLit : PatchChangedLit f cs of_ σ₀ τ sk :=
      ⟨cref, c, l, hget, hlmem, hvarOf, hltrue, hfalseFirst⟩
    exact ⟨cref, c, l, hget, hclauseFalse, hlmem, hvarOf, hltrue,
      hfalseFirst,
      patchChangedLit_implies_fiber
        f cs hexiOf hcontainsOf hchangedLit⟩
  · right
    have hneOf : l.var ≠ of_ := by
      intro hEq
      exact hnextNe (hvarNext.symm.trans hEq)
    have htrueFirst :
        f.litValue τ (patchDeleteWitnessAt f of_ σ₀ sk) l = true := by
      rw [dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
        f of_ σ₀ τ sk l hneOf]
      exact hltrue
    have hchangedLit :
        PatchChangedLit f cs nextOf σ τ
          (patchDeleteWitnessAt f of_ σ₀ sk) :=
      ⟨cref, c, l, hget, hlmem, hvarNext, htrueFirst, hlfalse⟩
    exact ⟨cref, c, l, hget, hclauseFalse, hlmem, hvarNext,
      htrueFirst, hlfalse,
      patchChangedLit_implies_fiber
        f cs hexiNext hcontainsNext hchangedLit⟩

theorem dependencyRemoval_twoPatch_changedClause_from_false
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase : SkolemAssignment} {leftLit rightLit : Literal}
    {σ τ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hleftVar : leftLit.var ∈ vars.toList)
    (hrightVar : rightLit.var ∈ vars.toList)
    (hdistinct : leftLit.var ≠ rightLit.var)
    (hallBase : ∀ ρ, s.clauses.matrixValue s.formula ρ skBase = true)
    (hfalse :
      s.clauses.matrixValue s.formula τ
        (patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ)
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase)) =
          false) :
    DependencyRemovalTwoPatchChangedClause s on_ skBase
      (patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ)
        (patchDeleteWitnessAt s.formula leftLit.var σ skBase))
      leftLit rightLit σ τ := by
  let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
  let sk₂ :=
    patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ) sk₁
  have hchanged :
      ∃ cref c l,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ sk₂ c.lits = false ∧
        l ∈ c.lits.toList ∧
        (l.var = leftLit.var ∨ l.var = rightLit.var) ∧
        s.formula.litValue τ skBase l = true ∧
        s.formula.litValue τ sk₂ l = false := by
    dsimp [sk₂, sk₁]
    exact dependencyRemoval_matrixValue_twoPatch_false_changedClause
      s.formula s.clauses leftLit.var rightLit.var σ
      (flipUniv on_ σ) τ skBase hallBase hfalse
  rcases dependencyRemoval_twoPatch_changedClause_cases
      s.formula s.clauses (of_ := leftLit.var)
      (nextOf := rightLit.var) (on_ := on_) (σ₀ := σ)
      (σ := flipUniv on_ σ) (τ := τ) (sk := skBase)
      (Ne.symm hdistinct) (hexi leftLit.var hleftVar)
      (hcontains leftLit.var hleftVar)
      (hexi rightLit.var hrightVar)
      (hcontains rightLit.var hrightVar)
      (by simpa [sk₂, sk₁] using hchanged) with
    hleft | hright
  · rcases hleft with
      ⟨cref, c, l, hget, hclauseFalse, hlmem, hvar, hltrue,
        hlfalse, hfiber⟩
    exact ⟨cref, c, l, hget, by simpa [sk₂, sk₁] using hclauseFalse,
      hlmem, Or.inl ⟨hvar, hltrue, hlfalse, hfiber⟩⟩
  · rcases hright with
      ⟨cref, c, l, hget, hclauseFalse, hlmem, hvar, hltrue,
        hlfalse, hfiber⟩
    exact ⟨cref, c, l, hget, by simpa [sk₂, sk₁] using hclauseFalse,
      hlmem, Or.inr ⟨hvar, hltrue, by simpa [sk₂, sk₁] using hlfalse,
        by simpa [sk₁] using hfiber⟩⟩

/-!
                This means there is some other literal  $l_y\in C$ with variable $y$
such that it is satisfied in $\gamma^u \cup f(\gamma^u)$. As we observed
that $f$ and $f'$ must agree on $\gamma^u$, $l_y$ is also satisfied by
$\gamma^u \cup f'(\gamma^u)$.
                $\gamma \cup f(\gamma)$ does not satisfy $l_y$ as it does not satisfy
clause $C$. Therefore the only universal variable $y$ can be is $u$,
however $l_y$ cannot be $l_u$, otherwise $\gamma \cup f(\gamma)$ would
satisfy this (we come back to this for pure paths), and  $l_y$ cannot be
$\bar l_u$ otherwise we would have $\bar l_u \not \pusim l_z$.
                Therefore $y$ is existential.
-/

/-- If the failed clause becomes true after flipping `on_`, some literal in
that same clause changed from false to true. In Lean this changed literal is
recorded as a `DeleteDepWitness`. If the same clause is still false after the
flip, we keep exactly that same-clause failure as the remaining branch. -/
theorem dependencyRemoval_falseClause_flipWitness_or_sameClauseFalse
    {s : CheckState} {on_ : Var}
    {sk : SkolemAssignment} {σ : UnivAssignment}
    {c : Clause}
    (hclauseFalse : s.formula.clauseValue σ sk c.lits = false) :
    (∃ flipLit,
      flipLit ∈ c.lits.toList ∧
      s.formula.litValue σ sk flipLit = false ∧
      s.formula.litValue (flipUniv on_ σ) sk flipLit = true ∧
      DeleteDepWitness s.formula flipLit.var on_ sk σ) ∨
    s.formula.clauseValue (flipUniv on_ σ) sk c.lits = false := by
  by_cases hflipClause :
      s.formula.clauseValue (flipUniv on_ σ) sk c.lits = true
  · left
    rcases clauseValue_false_true_flip_changed_lit
        s.formula on_ σ sk c.lits hclauseFalse hflipClause with
      ⟨flipLit, hmem, hfalse, htrue, hwit⟩
    exact ⟨flipLit, hmem, hfalse, htrue, hwit⟩
  · right
    cases hval :
        s.formula.clauseValue (flipUniv on_ σ) sk c.lits with
    | false => rfl
    | true => exact False.elim (hflipClause hval)

/-!
If the already-known changed literal is still false on the flipped assignment,
then any literal that makes the flipped clause true must be a different
literal.  This is the Lean version of the proof's "some other literal
\(l_y \in C\)" step.
-/

theorem dependencyRemoval_falseClause_flipOtherWitness_or_sameClauseFalse
    {s : CheckState} {on_ : Var}
    {sk : SkolemAssignment} {σ : UnivAssignment}
    {c : Clause} {baseLit : Literal}
    (hclauseFalse : s.formula.clauseValue σ sk c.lits = false)
    (hbaseFlipFalse :
      s.formula.litValue (flipUniv on_ σ) sk baseLit = false) :
    (∃ flipLit,
      flipLit ∈ c.lits.toList ∧
      flipLit ≠ baseLit ∧
      s.formula.litValue σ sk flipLit = false ∧
      s.formula.litValue (flipUniv on_ σ) sk flipLit = true ∧
      DeleteDepWitness s.formula flipLit.var on_ sk σ) ∨
    s.formula.clauseValue (flipUniv on_ σ) sk c.lits = false := by
  rcases dependencyRemoval_falseClause_flipWitness_or_sameClauseFalse
      (s := s) (on_ := on_) (sk := sk) (σ := σ)
      (c := c) hclauseFalse with
    hflip | hsame
  · left
    rcases hflip with
      ⟨flipLit, hmem, hfalse, htrue, hwit⟩
    have hne : flipLit ≠ baseLit := by
      intro hEq
      rw [hEq, hbaseFlipFalse] at htrue
      cases htrue
    exact ⟨flipLit, hmem, hne, hfalse, htrue, hwit⟩
  · exact Or.inr hsame

/-!
The exact two-patch residual repeats the same false-clause move one layer
deeper.  The changed literal in the residual false clause is false for the
two-patch candidate.  The next lemma shows that it is also false after flipping
\(u\).  This is the residual analogue of the TeX observation that the old
literal cannot be the literal that makes the flipped clause true.
-/

theorem dependencyRemoval_patchChangedFiber_changedLit_falseOnFlip
    (f : DQBF) (cs : ClauseStore) {of_ on_ : Var}
    {σSeed τ : UnivAssignment} {sk : SkolemAssignment} {l : Literal}
    (hexi : f.isVarExistential of_ = true)
    (hcontains : (f.depset.getD of_ #[]).contains on_ = true)
    (hwit : DeleteDepWitness f of_ on_ sk σSeed)
    (hfiber : PatchChangedFiber f cs of_ on_ σSeed τ sk)
    (hvar : l.var = of_)
    (hltrue : f.litValue τ sk l = true)
    (hlfalse :
      f.litValue τ (patchDeleteWitnessAt f of_ σSeed sk) l = false) :
    f.litValue (flipUniv on_ τ) (patchDeleteWitnessAt f of_ σSeed sk) l =
      false := by
  have hbaseτ :
      DeleteDepWitness f of_ on_ sk τ :=
    dependencyRemoval_deleteDepWitness_of_patchChangedFiber
      f cs hexi hwit hfiber
  have hnotPatch :
      ¬ DeleteDepWitness f of_ on_
        (patchDeleteWitnessAt f of_ σSeed sk) τ :=
    patchChangedFiber_removed_by_patch
      f cs hexi hcontains hwit hfiber
  have hchanged :
      f.varValue τ (patchDeleteWitnessAt f of_ σSeed sk) of_ ≠
        f.varValue τ sk of_ :=
    by
      simpa [hvar] using
        dependencyRemoval_litValue_true_false_varValue_ne
          f τ sk (patchDeleteWitnessAt f of_ σSeed sk) l hltrue
          hlfalse
  have holdFalse :
      f.litValue (flipUniv on_ τ)
          (patchDeleteWitnessAt f of_ σSeed sk)
          (mkLit of_ (f.varValue τ sk of_)) =
        false :=
    dependencyRemoval_removedChangedBaseWitness_oldLiteralFalseOnFlip
      f of_ on_ sk (patchDeleteWitnessAt f of_ σSeed sk) τ
      hbaseτ hnotPatch hchanged
  have hlEq : l = mkLit of_ (f.varValue τ sk of_) :=
    lit_eq_mkLit_varValue_of_var_and_true f of_ τ sk l hvar hltrue
  simpa [hlEq] using holdFalse

theorem dependencyRemoval_patchChangedFiber_changedLit_noPurePath
    {st : CheckState} (f : DQBF) (cs : ClauseStore) {of_ on_ : Var}
    {σSeed τ : UnivAssignment} {sk : SkolemAssignment} {l : Literal}
    (hexi : f.isVarExistential of_ = true)
    (hfiber : PatchChangedFiber f cs of_ on_ σSeed τ sk)
    (hvar : l.var = of_)
    (hltrue : f.litValue τ sk l = true)
    (hnoPathSeed :
      ¬ DeletePurePath st on_ (mkLit on_ (!(σSeed on_)))
        (mkLit of_ (f.varValue σSeed sk of_))) :
    ¬ DeletePurePath st on_ (mkLit on_ (!(τ on_))) l := by
  intro hpath
  have hvalueEq :
      f.varValue τ sk of_ = f.varValue σSeed sk of_ :=
    varValue_eq_of_fullDepArgs_eq f of_ τ σSeed sk hexi hfiber.2.1
  have hlEq : l = mkLit of_ (f.varValue σSeed sk of_) := by
    calc
      l = mkLit of_ (f.varValue τ sk of_) :=
        lit_eq_mkLit_varValue_of_var_and_true f of_ τ sk l hvar hltrue
      _ = mkLit of_ (f.varValue σSeed sk of_) := by rw [hvalueEq]
  have hstartEq :
      mkLit on_ (!(τ on_)) = mkLit on_ (!(σSeed on_)) := by
    rw [hfiber.2.2.2]
  exact hnoPathSeed (by simpa [hstartEq, hlEq] using hpath)

theorem dependencyRemoval_exactTwoPatchResidual_changedClause_flipFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ cref c changed τ,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      changed ∈ c.lits.toList ∧
      changed.var ∈ vars.toList ∧
      s.formula.litValue τ skBase changed = true ∧
      s.formula.litValue τ skNext changed = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed := by
  rcases hexact with
    ⟨_seedCref, _seedClause, leftLit, rightLit, τ, _hseedGet,
      _hleftMem, _hrightMem, hleftVar, hrightVar, hdistinct,
      hleftBase, _hleftNotCand, hrightBase, _hrightNotCand,
      hleftNoPath, hrightNoPath, _hfalseMatrix, hshape,
      hchangedClause, _hremoved⟩
  rcases hchangedClause with
    ⟨cref, c, changed, hget, hclauseFalse, hchangedMem,
      hchangedSide⟩
  let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
  rcases hchangedSide with hleft | hright
  · rcases hleft with
      ⟨hvar, htrueBase, hfalse₁, hfiber⟩
    have hfalseFlip₁ :
        s.formula.litValue (flipUniv on_ τ) sk₁ changed = false := by
      dsimp [sk₁]
      exact
        dependencyRemoval_patchChangedFiber_changedLit_falseOnFlip
          s.formula s.clauses (hexi leftLit.var hleftVar)
          (hcontains leftLit.var hleftVar) hleftBase hfiber hvar
          htrueBase hfalse₁
    have hchangedNeRight : changed.var ≠ rightLit.var := by
      intro hEq
      exact hdistinct (hvar.symm.trans hEq)
    have hfalseNextChanged :
        s.formula.litValue τ skNext changed = false := by
      rw [hshape]
      rw [dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
        s.formula rightLit.var (flipUniv on_ σ) τ
        (patchDeleteWitnessAt s.formula leftLit.var σ skBase)
        changed hchangedNeRight]
      simpa [sk₁] using hfalse₁
    have hfalseFlipNext :
        s.formula.litValue (flipUniv on_ τ) skNext changed = false := by
      rw [hshape]
      rw [dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
        s.formula rightLit.var (flipUniv on_ σ) (flipUniv on_ τ)
        (patchDeleteWitnessAt s.formula leftLit.var σ skBase)
        changed hchangedNeRight]
      simpa [sk₁] using hfalseFlip₁
    have hnoPathChanged :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed :=
      dependencyRemoval_patchChangedFiber_changedLit_noPurePath
        s.formula s.clauses (hexi leftLit.var hleftVar) hfiber hvar
        htrueBase hleftNoPath
    exact ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
      by simpa [hvar] using hleftVar, htrueBase, hfalseNextChanged,
      hfalseFlipNext, hnoPathChanged⟩
  · rcases hright with
      ⟨hvar, htrue₁, hfalseNext, hfiber⟩
    have hchangedNeLeft : changed.var ≠ leftLit.var := by
      intro hEq
      have hleftRight : leftLit.var = rightLit.var := by
        rw [← hEq, hvar]
      exact hdistinct hleftRight
    have htrueBase :
        s.formula.litValue τ skBase changed = true := by
      have htrueBase' :
          s.formula.litValue τ skBase changed =
            s.formula.litValue τ sk₁ changed := by
        dsimp [sk₁]
        rw [dependencyRemoval_litValue_patchDeleteWitnessAt_eq_of_ne_var
          s.formula leftLit.var σ τ skBase changed hchangedNeLeft]
      rw [htrueBase']
      exact htrue₁
    have hrightBase₁ :
        DeleteDepWitness s.formula rightLit.var on_ sk₁
          (flipUniv on_ σ) := by
      dsimp [sk₁]
      exact
        (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
          s.formula leftLit.var rightLit.var on_ σ
          (flipUniv on_ σ) skBase (Ne.symm hdistinct)).2
          hrightBase
    have hfalsePatch :
        s.formula.litValue τ
            (patchDeleteWitnessAt s.formula rightLit.var
              (flipUniv on_ σ) sk₁) changed = false := by
      rw [← hshape]
      exact hfalseNext
    have hfalseFlipPatch :
        s.formula.litValue (flipUniv on_ τ)
            (patchDeleteWitnessAt s.formula rightLit.var
              (flipUniv on_ σ) sk₁) changed = false :=
      dependencyRemoval_patchChangedFiber_changedLit_falseOnFlip
        s.formula s.clauses (hexi rightLit.var hrightVar)
        (hcontains rightLit.var hrightVar) hrightBase₁ hfiber hvar
        htrue₁ hfalsePatch
    have hfalseFlipNext :
        s.formula.litValue (flipUniv on_ τ) skNext changed = false := by
      rw [hshape]
      exact hfalseFlipPatch
    have hnoPathChanged :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed := by
      exact
        dependencyRemoval_patchChangedFiber_changedLit_noPurePath
          s.formula s.clauses (hexi rightLit.var hrightVar) hfiber
          hvar htrue₁ hrightNoPath
    exact ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
      by simpa [hvar] using hrightVar, htrueBase, hfalseNext,
      hfalseFlipNext, hnoPathChanged⟩

/-!
With the changed residual literal ruled out on the flipped side, the residual
false clause gives exactly the same dichotomy as the main TeX step: either
some other literal changes across the \(u\)-flip, or that same clause is still
false after the flip.
-/

theorem dependencyRemoval_exactTwoPatchResidual_otherWitness_or_sameClauseFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ cref c changed τ,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      changed ∈ c.lits.toList ∧
      changed.var ∈ vars.toList ∧
      s.formula.litValue τ skBase changed = true ∧
      s.formula.litValue τ skNext changed = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
      ((∃ flipLit,
        flipLit ∈ c.lits.toList ∧
        flipLit ≠ changed ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skNext τ) ∨
      s.formula.clauseValue (flipUniv on_ τ) skNext c.lits = false) := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_changedClause_flipFalse
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi hcontains hexact with
    ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
      hchangedVar, hchangedTrue, hchangedFalse, hchangedFlipFalse,
      hchangedNoPath⟩
  exact ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
    hchangedVar, hchangedTrue, hchangedFalse, hchangedFlipFalse,
    hchangedNoPath,
    dependencyRemoval_falseClause_flipOtherWitness_or_sameClauseFalse
      (s := s) (on_ := on_) (sk := skNext) (σ := τ)
      (c := c) (baseLit := changed) hclauseFalse hchangedFlipFalse⟩

/-- Here `baseLit` is the text's already-found literal `l_z`: it is true in
the original satisfying Skolem set, false in the current candidate, and has no
pure path from the flipped `on_` literal. The theorem proves the text's
"therefore `y` is existential" step: a universal flip literal would have to be
the start literal itself, which would create exactly the forbidden first pure
path to `baseLit`. -/
theorem dependencyRemoval_flipWitness_isExistential_or_sameClauseFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skCand : SkolemAssignment} {σ : UnivAssignment}
    {cref : CRef} {c : Clause} {baseLit : Literal}
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hget : s.clauses.getClause cref = some c)
    (hclauseFalse : s.formula.clauseValue σ skCand c.lits = false)
    (hbaseMem : baseLit ∈ c.lits.toList)
    (hbaseVar : baseLit.var ∈ vars.toList)
    (hbaseNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) baseLit) :
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      ((∃ flipLit,
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue σ skCand flipLit = false ∧
        s.formula.litValue (flipUniv on_ σ) skCand flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skCand σ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true) ∨
      s.formula.clauseValue (flipUniv on_ σ) skCand c.lits = false) := by
  classical
  have hnoCompl :
      ∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList := by
    intro l hl hneg
    have htaut :
        s.formula.clauseValue σ skCand c.lits = true :=
      clauseValue_true_of_mem_lit_and_negate
        s.formula σ skCand (lits := c.lits) (l := l) hl hneg
    rw [hclauseFalse] at htaut
    cases htaut
  refine ⟨hnoCompl, ?_⟩
  rcases dependencyRemoval_falseClause_flipWitness_or_sameClauseFalse
      (s := s) (on_ := on_) (sk := skCand) (σ := σ)
      (c := c) hclauseFalse with
    hflip | hflipFalse
  · rcases hflip with
      ⟨flipLit, hflipMem, hflipFalseLit, hflipTrueLit, hwit⟩
    by_cases hexiFlip : s.formula.isVarExistential flipLit.var = true
    · have hcontainsFlip :
          (s.formula.depset.getD flipLit.var #[]).contains on_ = true :=
        litValue_false_true_flip_existential_contains
          s.formula on_ σ skCand flipLit hexiFlip hflipFalseLit
          hflipTrueLit
      exact Or.inl ⟨flipLit, hflipMem, hflipFalseLit, hflipTrueLit, hwit,
        hexiFlip, hcontainsFlip⟩
    · have hunivFlip :
          s.formula.isVarExistential flipLit.var = false := by
        cases hval : s.formula.isVarExistential flipLit.var <;> simp_all
      have hvarOn : flipLit.var = on_ :=
        litValue_false_true_flip_universal_eq_on
          s.formula on_ σ skCand flipLit hunivFlip hflipFalseLit
          hflipTrueLit
      have hstartEq : flipLit = mkLit on_ (!(σ on_)) :=
        universal_lit_false_eq_mkLit_not_sigma
          s.formula on_ σ skCand flipLit hunivFlip hvarOn hflipFalseLit
      have hstartMem : mkLit on_ (!(σ on_)) ∈ c.lits.toList := by
        simpa [← hstartEq] using hflipMem
      have hnoStartNeg :
          (mkLit on_ (!(σ on_))).negate ∉ c.lits.toList := by
        simpa [← hstartEq] using hnoCompl flipLit hflipMem
      have hbaseNeStart : baseLit ≠ mkLit on_ (!(σ on_)) := by
        intro hEq
        have hvar := congrArg Literal.var hEq
        exact Nat.ne_of_gt (hgt baseLit.var hbaseVar)
          (by simpa [mkLit_var_early] using hvar)
      have hpathBase :
          DeletePurePath s on_ (mkLit on_ (!(σ on_))) baseLit :=
        DeletePurePath.first hget hstartMem hnoStartNeg hbaseMem
          hbaseNeStart (hexi baseLit.var hbaseVar)
          (hcontains baseLit.var hbaseVar)
      exact False.elim (hbaseNoPath hpathBase)
  · exact Or.inr hflipFalse

/-!
The same residual clause also supports the stronger TeX conclusion: if a
literal becomes true on the flipped assignment, it cannot be a universal
literal.  A universal flip literal would be the start literal, and the
tautology-free clause would then give the forbidden pure path to the already
changed literal.
-/

theorem dependencyRemoval_exactTwoPatchResidual_flipWitness_isExistential_or_sameClauseFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ cref c changed τ,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      changed ∈ c.lits.toList ∧
      changed.var ∈ vars.toList ∧
      s.formula.litValue τ skBase changed = true ∧
      s.formula.litValue τ skNext changed = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
      (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      ((∃ flipLit,
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true) ∨
      s.formula.clauseValue (flipUniv on_ τ) skNext c.lits = false) := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_changedClause_flipFalse
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi hcontains hexact with
    ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
      hchangedVar, hchangedTrue, hchangedFalse, hchangedFlipFalse,
      hchangedNoPath⟩
  rcases dependencyRemoval_flipWitness_isExistential_or_sameClauseFalse
      (s := s) (vars := vars) (on_ := on_) (skCand := skNext)
      (σ := τ) (cref := cref) (c := c) (baseLit := changed)
      hgt hexi hcontains hget hclauseFalse hchangedMem hchangedVar
      hchangedNoPath with
    ⟨hnoCompl, hflipOrFalse⟩
  exact ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
    hchangedVar, hchangedTrue, hchangedFalse, hchangedFlipFalse,
    hchangedNoPath, hnoCompl, hflipOrFalse⟩

theorem dependencyRemoval_sameClauseFailure_matrixFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfailure :
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ) :
    s.clauses.matrixValue s.formula σ skCand = false := by
  rcases hfailure with
    ⟨cref, c, _baseLit, hget, hclauseFalse, _hclauseFlipFalse,
      _hnoCompl, _hbaseMem, _hbaseVar, _hbaseTrue, _hbaseFalse,
      _hbaseNoPath⟩
  exact dependencyRemoval_matrixValue_false_of_false_clause
    s.formula s.clauses σ skCand hget hclauseFalse

/-!
Conversely, if the current candidate falsifies one concrete clause on both
\(u\)-sides, that is exactly the same-clause failure used in the TeX proof.
The original Skolem functions satisfy the clause, so some literal in the
clause changed from true to false.  The repair-pool invariant puts that
changed literal in the dependency-removal set and supplies the missing pure
path condition.
-/

theorem dependencyRemoval_currentClauseFalse_bothSides_sameClauseFailure
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    {cref : CRef} {c : Clause}
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hget : s.clauses.getClause cref = some c)
    (hclauseFalse : s.formula.clauseValue σ skCand c.lits = false)
    (hclauseFlipFalse :
      s.formula.clauseValue (flipUniv on_ σ) skCand c.lits = false) :
    FlexibleRepairSameClauseFlipFailure
      s vars on_ skBase skCand σ := by
  have hclauseBaseTrue :
      s.formula.clauseValue σ skBase c.lits = true :=
    clauseValue_of_matrixValue s.formula s.clauses σ skBase cref c
      (hallBase σ) hget
  rcases clauseValue_true_false_implies_exists_true_false_lit
      s.formula σ skBase skCand c.lits hclauseBaseTrue
      hclauseFalse with
    ⟨baseLit, hbaseMem, hbaseTrue, hbaseFalse⟩
  have hdiff :
      s.formula.varValue σ skCand baseLit.var ≠
        s.formula.varValue σ skBase baseLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand baseLit hbaseTrue hbaseFalse
  rcases htracked.1.2.2 baseLit.var σ hdiff with
    ⟨hbaseVar, hbaseNoPathValue⟩
  have hbaseEq :
      baseLit =
        mkLit baseLit.var (s.formula.varValue σ skBase baseLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula baseLit.var σ skBase baseLit rfl hbaseTrue
  have hbaseNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) baseLit := by
    rw [hbaseEq]
    exact hbaseNoPathValue
  have hnoCompl :
      ∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList := by
    intro l hl hneg
    have htaut :
        s.formula.clauseValue σ skCand c.lits = true :=
      clauseValue_true_of_mem_lit_and_negate
        s.formula σ skCand (lits := c.lits) (l := l) hl hneg
    rw [hclauseFalse] at htaut
    cases htaut
  exact ⟨cref, c, baseLit, hget, hclauseFalse, hclauseFlipFalse,
    hnoCompl, hbaseMem, hbaseVar, hbaseTrue, hbaseFalse, hbaseNoPath⟩

/-!
The previous split is now put in the same shape as the TeX induction step.
Either the flipped side supplies another existential dependency witness, or
the very same clause is false on both \(u\)-sides for the two-patch candidate.
-/

theorem dependencyRemoval_exactTwoPatchResidual_flipWitness_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    (∃ cref c changed flipLit τ,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      changed ∈ c.lits.toList ∧
      changed.var ∈ vars.toList ∧
      s.formula.litValue τ skBase changed = true ∧
      s.formula.litValue τ skNext changed = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
      (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      flipLit ∈ c.lits.toList ∧
      s.formula.litValue τ skNext flipLit = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
      DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
      s.formula.isVarExistential flipLit.var = true ∧
      (s.formula.depset.getD flipLit.var #[]).contains on_ = true) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_flipWitness_isExistential_or_sameClauseFalse
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hgt hexi hcontains hexact with
    ⟨cref, c, changed, τ, hget, hclauseFalse, hchangedMem,
      hchangedVar, hchangedTrue, hchangedFalse, _hchangedFlipFalse,
      hchangedNoPath, hnoCompl, hflipOrFalse⟩
  rcases hflipOrFalse with hflip | hsameClause
  · rcases hflip with
      ⟨flipLit, hflipMem, hflipFalse, hflipTrue, hwitNext,
        hexiFlip, hcontainsFlip⟩
    exact Or.inl
      ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        _hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipFalse, hflipTrue, hwitNext, hexiFlip, hcontainsFlip⟩
  · exact Or.inr
      ⟨τ, cref, c, changed, hget, hclauseFalse, hsameClause,
        hnoCompl, hchangedMem, hchangedVar, hchangedTrue,
        hchangedFalse, hchangedNoPath⟩

/-!
In the equivalent-footprint case, the same TeX split can be stated with the
next witness already transferred back to the current candidate.  The other
branch keeps the same-clause failure for the two-patch candidate, where it can
be fed into the next repair round.
-/

/-!
                Let


         \[ f''=\{f''_w \mid w \in E \}\quad
                f''_w(\tau) = \begin{cases}
                        \neg f'_w(\tau) & \text{ if } \tau = \gamma_y \text{ and } w=y\\
                        f'_w (\tau)     & \text{ otherwise,}
                \end{cases}
                \]
         we show that $f''\in\mpool$:
         \begin{enumerate}
                \item (+ smaller than $f'$) As $\gamma \cup f(\gamma)$ falsifies
$l_y$ and $\gamma \cup f(\gamma^u)$ satisfies $l_y$,
                $(\gamma_y, y, u)$ and  $(\gamma^u_y, y, u)$ are dependency witnesses
for $f'$ and therefore must be for $f$ by induction hypothesis.
$f''_y(\gamma_y)=  f''_y(\gamma^u_y)$ and thus these dependency
witnesses are removed for $f''$.
                For any dependency witness $(\delta, w, u)$ in $f''$, $w\neq y$ or
($\delta\neq \gamma_y$ and $\delta\neq \gamma_y^u$ ), and so
$f''_w(\delta)=f'_w(\delta)$ and $f''_w(\delta^u)=f'_w(\delta^u)$ so
$(\delta, w, u)$ is a dependency witness in $f'$ and thus also in $f$.
%This step also proves a strict subset of $f'$ as required.
                \item $f''$ only differs from $f'$ on $\gamma_y$ and its extensions.
                Since $(\gamma_y, y,u)$ is a dependency witness for $f'$, then $u\in
D(y)$, and since it is consistent with $\gamma$ then $\gamma_y$
satisfies $l_u$.
                \item $f_w^0$ only differs from $f'_w$ when $w=y$.
                We know that $(\gamma_y, y,u)$ is a dependency witness for $f$, so as
$f_y(\gamma^u_y)$ satisfies $l_y$ then $f_y(\gamma_y)$ satisfies $\bar
l_y$. Assume for contradiction, that $\bar l_u  \pusim \bar l_y$. We
know that if $l_u$ was in $C$ then $\gamma$ would satisfy $C$ which is
does not (this is the only observation needed to get from \Drrs to
\Dpu). Hence extending $\bar l_u  \pusim \bar l_y$ through the positive
$l_y$ to $l_z$ gives us a $\bar l_u$ pure path from $\bar l_u$ to $l_z$
giving us a contradiction.
         \end{enumerate}
-/

theorem dependencyRemoval_sameClause_tailOldLiteralNoPurePath
    {s : CheckState} {vars : Array Var} {on_ of_ nextOf : Var}
    {sk : SkolemAssignment} {σ : UnivAssignment}
    {cref : CRef} {c : Clause} {pos nextPos : Bool}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hof : of_ ∈ vars.toList)
    (hget : s.clauses.getClause cref = some c)
    (hmem : mkLit of_ pos ∈ c.lits.toList)
    (hnoPathToOriginal :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos))
    (hnextNe : nextOf ≠ of_)
    (hnextMem : mkLit nextOf nextPos ∈ c.lits.toList)
    (hothers :
      ∀ l ∈ c.lits.toList, l ≠ mkLit of_ pos →
        s.formula.litValue σ sk l = false) :
    ¬ DeletePurePath s on_
      (mkLit on_ (!(σ on_))) (mkLit nextOf (!nextPos)) :=
  oriented_dependent_tail_forces_next_old_lit_nonpath
    (s := s) (vars := vars) (on_ := on_) (of_ := of_)
    (nextOf := nextOf) (sk := sk) (σ := σ) (cref := cref)
    (c := c) (pos := pos) (nextPos := nextPos)
    hon_univ hexi hcontains hof hget hmem hnoPathToOriginal
    hnextNe hnextMem hothers

theorem dependencyRemoval_poolPatchStep_inRepairPool
    {s : CheckState} {vars : Array Var} {on_ patched : Var}
    {skBase skCand : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hpatched_mem : patched ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula patched on_ skCand σSeed)
    (hnoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit patched (s.formula.varValue σSeed skCand patched))) :
    FlexibleRepairPoolCandidate s vars on_ skBase
      (patchDeleteWitnessAt s.formula patched σSeed skCand) := by
  constructor
  · exact Nat.lt_trans
      (deleteWitnessFiberCountSet_patchDeleteWitnessAt_lt_of_mem
        s.formula vars patched on_ σSeed skCand hpatched_mem
        (hexi patched hpatched_mem) (hcontains patched hpatched_mem) hwit)
      hpool.1
  constructor
  · intro z hz args hfiber
    by_cases hz_patched : z = patched
    · subst z
      exact hpool.2.1 patched hpatched_mem args
        (deleteWitnessFiber_patchDeleteWitnessAt_imp_old_self
          s.formula patched on_ σSeed skCand args
          (hexi patched hpatched_mem) (hcontains patched hpatched_mem)
          hwit hfiber)
    · exact hpool.2.1 z hz args
        ((deleteWitnessFiber_patchDeleteWitnessAt_iff_of_ne
          s.formula patched z on_ σSeed skCand args hz_patched).1 hfiber)
  · intro z σ hdiff
    by_cases hcand_base :
        s.formula.varValue σ skCand z =
          s.formula.varValue σ skBase z
    · have hdiff_cand :
          s.formula.varValue σ
              (patchDeleteWitnessAt s.formula patched σSeed skCand) z ≠
            s.formula.varValue σ skCand z := by
        intro hsame
        exact hdiff (hsame.trans hcand_base)
      rcases varValue_patchDeleteWitnessAt_ne_implies_active_fullDepArgs
          s.formula patched σSeed σ skCand z
          (hexi patched hpatched_mem) hdiff_cand with
        ⟨hz_eq, hfull⟩
      subst z
      have hon_eq : σ on_ = σSeed on_ :=
        fullDepArgs_eq_implies_on_eq_of_contains
          s.formula patched on_ σ σSeed
          (hcontains patched hpatched_mem) hfull
      have hvar_eq :
          s.formula.varValue σ skCand patched =
            s.formula.varValue σSeed skCand patched :=
        varValue_eq_of_fullDepArgs_eq
          s.formula patched σ σSeed skCand
          (hexi patched hpatched_mem) hfull
      have hbase_eq :
          s.formula.varValue σ skBase patched =
            s.formula.varValue σSeed skCand patched := by
        rw [← hcand_base, hvar_eq]
      refine ⟨hpatched_mem, ?_⟩
      simpa [hon_eq, hbase_eq] using hnoPathSeed
    · exact hpool.2.2 z σ hcand_base

/-!
                The second pool condition in the TeX proof says that \(f''\)
only differs from \(f'\) on \(\gamma_y\) and assignments extending the same
dependency arguments.  In Lean, a Skolem function is indexed by the full
dependency argument vector, so "the same extensions" means equality of
`fullDepArgs`.  Since the patched variable depends on \(u\), this also gives
the same \(u\)-side as the seed assignment.
-/

theorem dependencyRemoval_patchStep_changedValue_is_seedSide
    {s : CheckState} {on_ patched z : Var}
    {skCand : SkolemAssignment} {σSeed σ : UnivAssignment}
    (hexiPatched : s.formula.isVarExistential patched = true)
    (hcontainsPatched :
      (s.formula.depset.getD patched #[]).contains on_ = true)
    (hdiff :
      s.formula.varValue σ
          (patchDeleteWitnessAt s.formula patched σSeed skCand) z ≠
        s.formula.varValue σ skCand z) :
    z = patched ∧
      fullDepArgs s.formula patched σ =
        fullDepArgs s.formula patched σSeed ∧
      σ on_ = σSeed on_ := by
  rcases varValue_patchDeleteWitnessAt_ne_implies_active_fullDepArgs
      s.formula patched σSeed σ skCand z hexiPatched hdiff with
    ⟨hz, hfull⟩
  have hon :
      σ on_ = σSeed on_ :=
    fullDepArgs_eq_implies_on_eq_of_contains
      s.formula patched on_ σ σSeed hcontainsPatched hfull
  exact ⟨hz, hfull, hon⟩

/-!
                The first pool condition in the TeX proof says that every
\(u\)-dependency witness left after the patch was already present before the
patch, and at least one witness fiber has been removed.  This is the direct
proper-subset form for a single patch step.
-/

theorem dependencyRemoval_poolPatchStep_currentWitnesses_properSubset
    {s : CheckState} {vars : Array Var} {on_ patched : Var}
    {skCand : SkolemAssignment} {σSeed : UnivAssignment}
    (hpatched_mem : patched ∈ vars.toList)
    (hexiPatched : s.formula.isVarExistential patched = true)
    (hcontainsPatched :
      (s.formula.depset.getD patched #[]).contains on_ = true)
    (hwit : DeleteDepWitness s.formula patched on_ skCand σSeed) :
    DeleteWitnessFiberSetProperSubset s.formula vars on_
      (patchDeleteWitnessAt s.formula patched σSeed skCand) skCand :=
  deleteWitnessFiberSetProperSubset_patchDeleteWitnessAt_of_mem
    s.formula vars patched on_ σSeed skCand hpatched_mem
    hexiPatched hcontainsPatched hwit

/-- The same local patch is also the strict descent step used by the induction:
the witness fiber for `patched` at `σSeed` is removed from the current
candidate before we continue. -/
theorem dependencyRemoval_poolPatchStep_strictStep
    {s : CheckState} {vars : Array Var} {on_ patched : Var}
    {skBase skCand : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hpatched_mem : patched ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula patched on_ skCand σSeed)
    (hnoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit patched (s.formula.varValue σSeed skCand patched))) :
    FlexibleRepairStrictStep s vars on_ skBase skCand := by
  let skNext := patchDeleteWitnessAt s.formula patched σSeed skCand
  refine ⟨skNext, ?_, ?_⟩
  · exact dependencyRemoval_poolPatchStep_inRepairPool
      (s := s) (vars := vars) (on_ := on_) (patched := patched)
      (skBase := skBase) (skCand := skCand) (σSeed := σSeed)
      hexi hcontains hpool hpatched_mem hwit hnoPathSeed
  · exact deleteWitnessFiberCountSet_patchDeleteWitnessAt_lt_of_mem
      s.formula vars patched on_ σSeed skCand hpatched_mem
      (hexi patched hpatched_mem) (hcontains patched hpatched_mem) hwit

theorem dependencyRemoval_poolPatchStep_trackedStrictStep
    {s : CheckState} {vars : Array Var} {on_ patched : Var}
    {skBase skCand : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hpatched_mem : patched ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula patched on_ skCand σSeed)
    (hnoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit patched (s.formula.varValue σSeed skCand patched))) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand := by
  let skNext := patchDeleteWitnessAt s.formula patched σSeed skCand
  refine ⟨skNext, ?_, ?_⟩
  · exact flexibleRepairPoolTracked_patch_step
      (s := s) (vars := vars) (on_ := on_) (patched := patched)
      (skBase := skBase) (skCand := skCand) (σSeed := σSeed)
      hexi hcontains htracked hpatched_mem hwit hnoPathSeed
  · exact deleteWitnessFiberCountSet_patchDeleteWitnessAt_lt_of_mem
      s.formula vars patched on_ σSeed skCand hpatched_mem
      (hexi patched hpatched_mem) (hcontains patched hpatched_mem) hwit

theorem dependencyRemoval_trackedStrictStep_of_flipWitnessNoStartPath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {startPos : Bool} {skBase skCand : SkolemAssignment}
    {σ : UnivAssignment} {lit : Literal}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hlit_var : lit.var ∈ vars.toList)
    (hon_eq : σ on_ = startPos)
    (hwit : DeleteDepWitness s.formula lit.var on_ skCand σ)
    (hflip_true : s.formula.litValue (flipUniv on_ σ) skCand lit = true)
    (hbase_eq : lit = mkLit lit.var (s.formula.varValue σ skBase lit.var))
    (hno_start_base :
      ¬ DeletePurePath s on_ (mkLit on_ startPos)
        (mkLit lit.var (s.formula.varValue σ skBase lit.var))) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand := by
  let σFlip := flipUniv on_ σ
  have hwitFlip :
      DeleteDepWitness s.formula lit.var on_ skCand σFlip := by
    have hflip_involutive : flipUniv on_ σFlip = σ := by
      funext v
      by_cases hv : v = on_
      · subst v
        simp [σFlip, flipUniv]
      · simp [σFlip, flipUniv, hv]
    unfold DeleteDepWitness at hwit ⊢
    rw [hflip_involutive]
    exact hwit.symm
  have hflip_lit_eq :
      lit =
        mkLit lit.var (s.formula.varValue σFlip skCand lit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula lit.var σFlip skCand lit rfl hflip_true
  have hstart_eq :
      mkLit on_ (!(σFlip on_)) = mkLit on_ startPos := by
    simp [σFlip, flipUniv, hon_eq]
  have hend_eq :
      mkLit lit.var (s.formula.varValue σFlip skCand lit.var) =
        mkLit lit.var (s.formula.varValue σ skBase lit.var) := by
    calc
      mkLit lit.var (s.formula.varValue σFlip skCand lit.var) = lit :=
        hflip_lit_eq.symm
      _ = mkLit lit.var (s.formula.varValue σ skBase lit.var) :=
        hbase_eq
  have hnoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σFlip on_)))
        (mkLit lit.var (s.formula.varValue σFlip skCand lit.var)) := by
    simpa [hstart_eq, hend_eq] using hno_start_base
  exact dependencyRemoval_poolPatchStep_trackedStrictStep
    (s := s) (vars := vars) (on_ := on_) (patched := lit.var)
    (skBase := skBase) (skCand := skCand) (σSeed := σFlip)
    hexi hcontains htracked hlit_var hwitFlip hnoPathSeed

/-- Once the flipped literal is known to be an existential whose dependency set
contains `on_`, closure of `vars` puts it in the repair set. If there is no
pure path to its current candidate literal, the local patch is the next strict
descent; otherwise the path is the remaining branch to discharge. -/
theorem dependencyRemoval_existentialFlipWitness_strictStep_or_purePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    {flipLit : Literal}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hwit : DeleteDepWitness s.formula flipLit.var on_ skCand σ)
    (hexiFlip : s.formula.isVarExistential flipLit.var = true)
    (hcontainsFlip :
      (s.formula.depset.getD flipLit.var #[]).contains on_ = true) :
    FlexibleRepairStrictStep s vars on_ skBase skCand ∨
      DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit flipLit.var (s.formula.varValue σ skCand flipLit.var)) := by
  classical
  have hflipVar : flipLit.var ∈ vars.toList :=
    hclosed flipLit.var hexiFlip hcontainsFlip
  by_cases hnoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit flipLit.var (s.formula.varValue σ skCand flipLit.var))
  · left
    exact dependencyRemoval_poolPatchStep_strictStep
      (s := s) (vars := vars) (on_ := on_) (patched := flipLit.var)
      (skBase := skBase) (skCand := skCand) (σSeed := σ)
      hexi hcontains hpool hflipVar hwit hnoPath
  · exact Or.inr (Classical.byContradiction hnoPath)

theorem dependencyRemoval_existentialFlipWitness_trackedStrictStep_or_purePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    {flipLit : Literal}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hwit : DeleteDepWitness s.formula flipLit.var on_ skCand σ)
    (hexiFlip : s.formula.isVarExistential flipLit.var = true)
    (hcontainsFlip :
      (s.formula.depset.getD flipLit.var #[]).contains on_ = true) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit flipLit.var (s.formula.varValue σ skCand flipLit.var)) := by
  classical
  have hflipVar : flipLit.var ∈ vars.toList :=
    hclosed flipLit.var hexiFlip hcontainsFlip
  by_cases hnoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit flipLit.var (s.formula.varValue σ skCand flipLit.var))
  · left
    exact dependencyRemoval_poolPatchStep_trackedStrictStep
      (s := s) (vars := vars) (on_ := on_) (patched := flipLit.var)
      (skBase := skBase) (skCand := skCand) (σSeed := σ)
      hexi hcontains htracked hflipVar hwit hnoPath
  · exact Or.inr (Classical.byContradiction hnoPath)

/-!
In the residual two-patch clause, the next flip witness has two possible
statuses relative to the current candidate \(f'\).  If it is already a
witness of \(f'\), the ordinary local patch either gives a strict descent or
leaves the named pure-path obstruction.  If it is not a witness of \(f'\),
then it is a genuinely new witness introduced by the two-patch candidate.

This is the Lean split between the equivalent-footprint branch and the
proper-growth branch.
-/

theorem dependencyRemoval_exactTwoPatchResidual_currentStep_or_newWitness_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      (∃ cref c changed flipLit τ,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skBase changed = true ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
        DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit flipLit.var
            (s.formula.varValue τ skCand flipLit.var))) ∨
      (∃ cref c changed flipLit τ,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skBase changed = true ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        flipLit.var ∈ vars.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
        ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  classical
  rcases
      dependencyRemoval_exactTwoPatchResidual_flipWitness_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hgt hexi hcontains hexact with
    hflip | hsameClause
  · rcases hflip with
      ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipFalse, hflipTrue, hwitNext, hexiFlip, hcontainsFlip⟩
    by_cases hwitCand :
        DeleteDepWitness s.formula flipLit.var on_ skCand τ
    · rcases
        dependencyRemoval_existentialFlipWitness_trackedStrictStep_or_purePath
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skCand) (σ := τ) (flipLit := flipLit)
          hclosed hexi hcontains htracked hwitCand hexiFlip
          hcontainsFlip with
        hstrict | hpath
      · exact Or.inl hstrict
      · exact Or.inr (Or.inl
          ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
            hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
            hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
            hflipFalse, hflipTrue, hwitCand, hexiFlip, hcontainsFlip,
            hpath⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hclosed flipLit.var hexiFlip hcontainsFlip, hflipFalse,
          hflipTrue, hwitNext, hwitCand, hexiFlip, hcontainsFlip⟩))
  · exact Or.inr (Or.inr (Or.inr hsameClause))

/-!
In the proper-growth side of the split, the witness found in the two-patch
candidate is absent from the current candidate.  The repair-pool tracking
invariant turns that absence into the same TeX observation used earlier:
on one of the two \(u\)-sides, the current candidate differs from the original
Skolem functions, the original literal has no pure path from that side, and
that original literal is false after flipping \(u\).
-/

theorem dependencyRemoval_newWitness_currentFlipObservation
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand skNext : SkolemAssignment} {τ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedCand :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hof : of_ ∈ vars.toList)
    (hwitNext : DeleteDepWitness s.formula of_ on_ skNext τ)
    (hnotCand : ¬ DeleteDepWitness s.formula of_ on_ skCand τ) :
    ∃ σSide,
      (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
      DeleteDepWitness s.formula of_ on_ skBase σSide ∧
      ¬ DeleteDepWitness s.formula of_ on_ skCand σSide ∧
      s.formula.varValue σSide skCand of_ ≠
        s.formula.varValue σSide skBase of_ ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
        (mkLit of_ (s.formula.varValue σSide skBase of_)) ∧
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit of_ (s.formula.varValue σSide skBase of_)) = false ∧
      ∀ ρ,
        deleteDepArgs s.formula of_ on_ ρ =
          deleteDepArgs s.formula of_ on_ σSide →
        s.formula.varValue ρ skCand of_ ≠
          s.formula.varValue ρ skBase of_ →
        fullDepArgs s.formula of_ ρ =
          fullDepArgs s.formula of_ σSide := by
  rcases
      flexibleRepairPoolTracked_missing_liveWitness_changed_footprint
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (skBase := skBase) (skCand := skCand) (skNext := skNext)
        (σ := τ) (hexi of_ hof) htrackedCand htrackedNext hof
        hwitNext hnotCand with
    ⟨σSide, hside, _hof, hbaseSide, hchanged, hfiber⟩
  rcases dependencyRemoval_changedValue_baseWitnessAndNoPath
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (skBase := skBase) (skCand := skCand) (σ := σSide)
      htrackedCand hchanged with
    ⟨_hof, _hbaseSide, hnoPath⟩
  have hnotSide :
      ¬ DeleteDepWitness s.formula of_ on_ skCand σSide := by
    rcases hside with hside | hside
    · simpa [hside] using hnotCand
    · intro hwitSide
      have hwitτ :
          DeleteDepWitness s.formula of_ on_ skCand τ :=
        (dependencyRemoval_deleteDepWitness_flipUniv_iff
          s.formula of_ on_ skCand τ).1 (by
            simpa [hside] using hwitSide)
      exact hnotCand hwitτ
  have holdFalse :
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit of_ (s.formula.varValue σSide skBase of_)) = false :=
    dependencyRemoval_removedChangedBaseWitness_oldLiteralFalseOnFlip
      s.formula of_ on_ skBase skCand σSide
      hbaseSide hnotSide hchanged
  exact ⟨σSide, hside, hbaseSide, hnotSide, hchanged, hnoPath,
    holdFalse, hfiber⟩

/-!
Combining the previous observation with the residual split gives the next
TeX-shaped case distinction.  Either the current candidate already has a
strict repair step, or the residual has the named pure-path obstruction, or
the witness introduced by the two-patch candidate is accompanied by the
current candidate's old-literal observation, or the two-patch candidate is
still in the same-clause-false branch.
-/

theorem dependencyRemoval_exactTwoPatchResidual_currentStep_or_newWitnessObservation_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext : FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      (∃ cref c changed flipLit τ,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skBase changed = true ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
        DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit flipLit.var
            (s.formula.varValue τ skCand flipLit.var))) ∨
      (∃ cref c changed flipLit τ σSide,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skBase changed = true ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        flipLit.var ∈ vars.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
        ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
        (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
        DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
        ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
        s.formula.varValue σSide skCand flipLit.var ≠
          s.formula.varValue σSide skBase flipLit.var ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
          (mkLit flipLit.var
            (s.formula.varValue σSide skBase flipLit.var)) ∧
        s.formula.litValue (flipUniv on_ σSide) skCand
          (mkLit flipLit.var
            (s.formula.varValue σSide skBase flipLit.var)) = false ∧
        ∀ ρ,
          deleteDepArgs s.formula flipLit.var on_ ρ =
            deleteDepArgs s.formula flipLit.var on_ σSide →
          s.formula.varValue ρ skCand flipLit.var ≠
            s.formula.varValue ρ skBase flipLit.var →
          fullDepArgs s.formula flipLit.var ρ =
            fullDepArgs s.formula flipLit.var σSide) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  classical
  rcases
      dependencyRemoval_exactTwoPatchResidual_currentStep_or_newWitness_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hclosed hgt hexi hcontains htracked hexact with
    hstrict | hrest
  · exact Or.inl hstrict
  · rcases hrest with hpath | hrest
    · exact Or.inr (Or.inl hpath)
    · rcases hrest with hnew | hsameClause
      · rcases hnew with
          ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
            hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
            hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
            hflipVar, hflipFalse, hflipTrue, hwitNext, hnotCand,
            hexiFlip, hcontainsFlip⟩
        rcases
            dependencyRemoval_newWitness_currentFlipObservation
              (s := s) (vars := vars) (on_ := on_)
              (of_ := flipLit.var) (skBase := skBase)
              (skCand := skCand) (skNext := skNext) (τ := τ)
              hexi htracked htrackedNext hflipVar hwitNext hnotCand with
          ⟨σSide, hside, hbaseSide, hnotSide, hchangedCurrent,
            hnoPathCurrent, holdFalse, hfiber⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨cref, c, changed, flipLit, τ, σSide, hget,
            hclauseFalse, hchangedMem, hchangedVar, hchangedTrue,
            hchangedFalse, hchangedFlipFalse, hchangedNoPath, hnoCompl,
            hflipMem, hflipVar, hflipFalse, hflipTrue, hwitNext,
            hnotCand, hexiFlip, hcontainsFlip, hside, hbaseSide,
            hnotSide, hchangedCurrent, hnoPathCurrent, holdFalse,
            hfiber⟩))
      · exact Or.inr (Or.inr (Or.inr hsameClause))

/-!
In the equivalent-footprint case, a witness present in the two-patch
candidate cannot be new relative to the current candidate: the footprint
subset from the two-patch candidate back to the current candidate transfers
the witness back.
-/

theorem dependencyRemoval_subsetNextCand_forbids_newWitness
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skCand skNext : SkolemAssignment} {τ : UnivAssignment}
    (hexiOf : s.formula.isVarExistential of_ = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hof : of_ ∈ vars.toList)
    (hwitNext : DeleteDepWitness s.formula of_ on_ skNext τ)
    (hnotCand : ¬ DeleteDepWitness s.formula of_ on_ skCand τ) :
    False := by
  have hwitCand :
      DeleteDepWitness s.formula of_ on_ skCand τ :=
    Classical.byContradiction (fun hnotCand' =>
      (deleteWitnessFiberSetSubset_not_deleteDepWitness
        (f := s.formula) (vars := vars) (on_ := on_)
        (of_ := of_) (skSmall := skNext) (skBig := skCand)
        (σ := τ) hexiOf hsubsetNextCand hof hnotCand') hwitNext)
  exact hnotCand hwitCand

/-!
After the equivalent-footprint transfer, the ordinary repair-pool patch lemma
applies again.  The equivalent-footprint residual therefore either gives a
strict descent from the current candidate, or leaves a named pure-path
obstruction, or stays in the same-clause-false branch.
-/

theorem dependencyRemoval_exactTwoPatchResidual_equivalentStrictStep_or_path_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext : FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      (∃ cref c changed flipLit τ,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
        DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit flipLit.var
            (s.formula.varValue τ skCand flipLit.var))) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_currentStep_or_newWitnessObservation_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hclosed hgt hexi hcontains htracked htrackedNext hexact with
    hstrict | hrest
  · exact Or.inl hstrict
  · rcases hrest with hpath | hrest
    · rcases hpath with
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, _hchangedTrue, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hflipFalse, hflipTrue, hwitCand, hexiFlip, hcontainsFlip,
          hpath⟩
      exact Or.inr (Or.inl
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, hchangedFalse, hchangedFlipFalse,
          hchangedNoPath, hnoCompl, hflipMem, hflipFalse, hflipTrue,
          hwitCand, hexiFlip, hcontainsFlip, hpath⟩)
    · rcases hrest with hnew | hsameClause
      · rcases hnew with
          ⟨_cref, _c, _changed, flipLit, τ, _σSide, _hget,
            _hclauseFalse, _hchangedMem, _hchangedVar,
            _hchangedTrue, _hchangedFalse, _hchangedFlipFalse,
            _hchangedNoPath, _hnoCompl, _hflipMem, hflipVar,
            _hflipFalse, _hflipTrue, hwitNext, hnotCand,
            hexiFlip, _hcontainsFlip, _hside, _hbaseSide,
            _hnotSide, _hchangedCurrent, _hnoPathCurrent, _holdFalse,
            _hfiber⟩
        exact False.elim
          (dependencyRemoval_subsetNextCand_forbids_newWitness
            (s := s) (vars := vars) (on_ := on_)
            (of_ := flipLit.var) (skCand := skCand)
            (skNext := skNext) (τ := τ)
            hexiFlip hsubsetNextCand hflipVar hwitNext hnotCand)
      · exact Or.inr (Or.inr hsameClause)

/-!
In the equivalent-footprint residual, Lean now has both pieces of TeX data in
one place.  The current frontier supplies the already-removed old literal and
its missing pure path.  The exact residual then says what still remains:
either patching the current candidate is already a strict descent, or there is
a named pure-path obstruction, or the same-clause failure has moved to the
two-patch candidate.
-/

theorem dependencyRemoval_currentFrontier_equivalentFootprint_oldLiteral_and_nextCases
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext : FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hcurrent :
      DependencyRemovalCurrentResidualFrontier
        s vars on_ skBase skCand skNext σ)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    (∃ patched τPatch σSide,
      patched ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula patched on_ skCand τPatch ∧
      DeleteDepWitness s.formula patched on_ skBase τPatch ∧
      (σSide = τPatch ∨ σSide = flipUniv on_ τPatch) ∧
      DeleteDepWitness s.formula patched on_ skBase σSide ∧
      s.formula.varValue σSide skCand patched ≠
        s.formula.varValue σSide skBase patched ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
        (mkLit patched (s.formula.varValue σSide skBase patched)) ∧
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit patched (s.formula.varValue σSide skBase patched)) =
          false ∧
      ∀ ρ,
        deleteDepArgs s.formula patched on_ ρ =
          deleteDepArgs s.formula patched on_ σSide →
        s.formula.varValue ρ skCand patched ≠
          s.formula.varValue ρ skBase patched →
        fullDepArgs s.formula patched ρ =
          fullDepArgs s.formula patched σSide) ∧
    (FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      (∃ cref c changed flipLit τ,
        s.clauses.getClause cref = some c ∧
        s.formula.clauseValue τ skNext c.lits = false ∧
        changed ∈ c.lits.toList ∧
        changed.var ∈ vars.toList ∧
        s.formula.litValue τ skNext changed = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
        (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
        flipLit ∈ c.lits.toList ∧
        s.formula.litValue τ skNext flipLit = false ∧
        s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
        DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
        s.formula.isVarExistential flipLit.var = true ∧
        (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
        DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit flipLit.var
            (s.formula.varValue τ skCand flipLit.var))) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ) := by
  constructor
  · exact dependencyRemoval_currentFrontier_flipObservation
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hcurrent
  · exact
      dependencyRemoval_exactTwoPatchResidual_equivalentStrictStep_or_path_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hclosed hgt hexi hcontains htracked htrackedNext
        hsubsetNextCand hexact

/-- The "pure path branch" still gives a strict descent. The path branch says:
the candidate failed on a clause, the base-changing literal has no pure path
from this side of `on_`, but the flip-changing literal does have such a path.
The no-cross-path hypothesis then forbids the opposite start path, so we patch
at the flipped universal assignment instead. -/
theorem dependencyRemoval_pathBranch_strictStep
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hbranch : FlexibleRepairPathBranch s vars on_ skBase skCand σ) :
    FlexibleRepairStrictStep s vars on_ skBase skCand := by
  let startPos := σ on_
  have hblocked :
      PatchPoolBlockedPathBranch s vars on_ startPos skBase skCand :=
    flexibleRepairPathBranch_to_blockedPathBranch
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ)
      hon_univ hexi hcontains hbranch
  rcases patchPoolBlockedPathBranch_value_path_certificate
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (startPos := startPos) (skBase := skBase)
      (skCand := skCand)
      hfull hon_le hon_univ hpaths hblocked with
    ⟨σPath, _cref, _c, lit, _hget, _hclauseFalse, _hnoCompl,
      _hlitMem, hlitVar, honEq, _hlitTrue, _hlitFalse, hwit,
      hflipTrue, hbaseEq, _hcandEq, _hpathCand, _hnoOppositeBase,
      hnoStartBase⟩
  exact flexibleRepairStrictStep_of_flip_witness_no_start_path
    (s := s) (vars := vars) (on_ := on_) (startPos := startPos)
    (skBase := skBase) (skStop := skCand) (σ := σPath) (lit := lit)
    hexi hcontains hpool hlitVar honEq hwit hflipTrue hbaseEq
    hnoStartBase

theorem dependencyRemoval_pathBranch_trackedStrictStep
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hbranch : FlexibleRepairPathBranch s vars on_ skBase skCand σ) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand := by
  let startPos := σ on_
  have hblocked :
      PatchPoolBlockedPathBranch s vars on_ startPos skBase skCand :=
    flexibleRepairPathBranch_to_blockedPathBranch
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ)
      hon_univ hexi hcontains hbranch
  rcases patchPoolBlockedPathBranch_value_path_certificate
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (startPos := startPos) (skBase := skBase)
      (skCand := skCand)
      hfull hon_le hon_univ hpaths hblocked with
    ⟨σPath, _cref, _c, lit, _hget, _hclauseFalse, _hnoCompl,
      _hlitMem, hlitVar, honEq, _hlitTrue, _hlitFalse, hwit,
      hflipTrue, hbaseEq, _hcandEq, _hpathCand, _hnoOppositeBase,
      hnoStartBase⟩
  exact dependencyRemoval_trackedStrictStep_of_flipWitnessNoStartPath
    (s := s) (vars := vars) (on_ := on_) (startPos := startPos)
    (skBase := skBase) (skCand := skCand) (σ := σPath) (lit := lit)
    hexi hcontains htracked hlitVar honEq hwit hflipTrue hbaseEq
    hnoStartBase

/-- A blocked path branch is not terminal. The path certificate supplies the
same data used in the TeX "other literal" chase: a changed existential literal
whose flipped assignment is true, together with the no-start-path fact forced
by the no-cross-path hypothesis. Patching that flipped witness is therefore a
strict tracked repair step. -/
theorem dependencyRemoval_blockedPathBranch_trackedStrictStep
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {startPos : Bool} {skBase skCand : SkolemAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hbranch :
      PatchPoolBlockedPathBranch s vars on_ startPos skBase skCand) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand := by
  rcases patchPoolBlockedPathBranch_value_path_certificate
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (startPos := startPos) (skBase := skBase)
      (skCand := skCand)
      hfull hon_le hon_univ hpaths hbranch with
    ⟨σPath, _cref, _c, lit, _hget, _hclauseFalse, _hnoCompl,
      _hlitMem, hlitVar, honEq, _hlitTrue, _hlitFalse, hwit,
      hflipTrue, hbaseEq, _hcandEq, _hpathCand, _hnoOppositeBase,
      hnoStartBase⟩
  exact dependencyRemoval_trackedStrictStep_of_flipWitnessNoStartPath
    (s := s) (vars := vars) (on_ := on_) (startPos := startPos)
    (skBase := skBase) (skCand := skCand) (σ := σPath) (lit := lit)
    hexi hcontains htracked hlitVar honEq hwit hflipTrue hbaseEq
    hnoStartBase

/-- A failed pool candidate either has an immediate strict repair step, has the
path branch described above, or the same candidate also fails on the flipped
universal assignment. This is the TeX case split around the literal `l_y`. -/
theorem dependencyRemoval_failedCandidate_strictStep_or_pathBranch_or_sameClauseFailure
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    FlexibleRepairStrictStep s vars on_ skBase skCand ∨
      FlexibleRepairPathBranch s vars on_ skBase skCand σ ∨
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ := by
  rcases dependencyRemoval_falsifiedClause_changedLiteral
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ) hpool hallBase hfalse with
    ⟨cref, c, baseLit, hget, hclauseFalse, hbaseMem, hbaseVar,
      hbaseTrue, hbaseFalse, hbaseNoPath⟩
  rcases dependencyRemoval_flipWitness_isExistential_or_sameClauseFalse
      (s := s) (vars := vars) (on_ := on_) (skCand := skCand)
      (σ := σ) (cref := cref) (c := c) (baseLit := baseLit)
      hgt hexi hcontains hget hclauseFalse hbaseMem hbaseVar hbaseNoPath with
    ⟨hnoCompl, hflipOrFalse⟩
  rcases hflipOrFalse with hflip | hflipFalse
  · rcases hflip with
      ⟨flipLit, hflipMem, hflipFalseLit, hflipTrueLit, hwit,
        hexiFlip, hcontainsFlip⟩
    rcases dependencyRemoval_existentialFlipWitness_strictStep_or_purePath
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (flipLit := flipLit)
        hclosed hexi hcontains hpool hwit hexiFlip hcontainsFlip with
      hstrict | hpath
    · exact Or.inl hstrict
    · right
      left
      exact ⟨cref, c, baseLit, flipLit, hget, hclauseFalse, hnoCompl,
        hbaseMem, hbaseVar, hbaseTrue, hbaseFalse, hbaseNoPath,
        hflipMem, hclosed flipLit.var hexiFlip hcontainsFlip,
        hflipFalseLit, hflipTrueLit, hwit, hpath⟩
  · exact Or.inr (Or.inr
      ⟨cref, c, baseLit, hget, hclauseFalse, hflipFalse, hnoCompl,
        hbaseMem, hbaseVar, hbaseTrue, hbaseFalse, hbaseNoPath⟩)

theorem dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_pathBranch_or_sameClauseFailure
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      FlexibleRepairPathBranch s vars on_ skBase skCand σ ∨
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ := by
  rcases dependencyRemoval_falsifiedClause_changedLiteral
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ) htracked.1 hallBase hfalse with
    ⟨cref, c, baseLit, hget, hclauseFalse, hbaseMem, hbaseVar,
      hbaseTrue, hbaseFalse, hbaseNoPath⟩
  rcases dependencyRemoval_flipWitness_isExistential_or_sameClauseFalse
      (s := s) (vars := vars) (on_ := on_) (skCand := skCand)
      (σ := σ) (cref := cref) (c := c) (baseLit := baseLit)
      hgt hexi hcontains hget hclauseFalse hbaseMem hbaseVar hbaseNoPath with
    ⟨hnoCompl, hflipOrFalse⟩
  rcases hflipOrFalse with hflip | hflipFalse
  · rcases hflip with
      ⟨flipLit, hflipMem, hflipFalseLit, hflipTrueLit, hwit,
        hexiFlip, hcontainsFlip⟩
    rcases dependencyRemoval_existentialFlipWitness_trackedStrictStep_or_purePath
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (flipLit := flipLit)
        hclosed hexi hcontains htracked hwit hexiFlip hcontainsFlip with
      hstrict | hpath
    · exact Or.inl hstrict
    · right
      left
      exact ⟨cref, c, baseLit, flipLit, hget, hclauseFalse, hnoCompl,
        hbaseMem, hbaseVar, hbaseTrue, hbaseFalse, hbaseNoPath,
        hflipMem, hclosed flipLit.var hexiFlip hcontainsFlip,
        hflipFalseLit, hflipTrueLit, hwit, hpath⟩
  · exact Or.inr (Or.inr
      ⟨cref, c, baseLit, hget, hclauseFalse, hflipFalse, hnoCompl,
        hbaseMem, hbaseVar, hbaseTrue, hbaseFalse, hbaseNoPath⟩)

theorem dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_sameClauseFailure
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ := by
  rcases
      dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_pathBranch_or_sameClauseFailure
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hclosed hgt hexi hcontains htracked hallBase hfalse with
    hstrict | hrest
  · exact Or.inl hstrict
  · rcases hrest with hbranch | hflipFalse
    · exact Or.inl
        (dependencyRemoval_pathBranch_trackedStrictStep
          (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
          (on_ := on_) (skBase := skBase) (skCand := skCand) (σ := σ)
          hfull hon_le hon_univ hexi hcontains hpaths htracked hbranch)
    · exact Or.inr hflipFalse

/-!
                If the same clause is false both before and after flipping $u$,
                the original satisfying Skolem functions still make that clause
true at $\gamma^u$.  Therefore there is another literal in the same clause
which is true for $f$ and false for $f'$ on the flipped side.  Lean records
this as a two-polarity same-clause failure: one changed literal is seen at
$\gamma$, and one changed literal is seen at $\gamma^u$.
-/

theorem dependencyRemoval_sameClauseFailure_twoPolarity
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfailure :
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ) :
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ := by
  rcases hfailure with
    ⟨cref, c, leftLit, hget, hclauseFalse, hclauseFlipFalse,
      hnoCompl, hleftMem, hleftVar, hleftTrue, hleftFalse,
      hleftNoPath⟩
  have hclauseFlipTrueBase :
      s.formula.clauseValue (flipUniv on_ σ) skBase c.lits = true :=
    clauseValue_of_matrixValue s.formula s.clauses (flipUniv on_ σ)
      skBase cref c (hallBase (flipUniv on_ σ)) hget
  rcases clauseValue_true_false_implies_exists_true_false_lit
      s.formula (flipUniv on_ σ) skBase skCand c.lits
      hclauseFlipTrueBase hclauseFlipFalse with
    ⟨rightLit, hrightMem, hrightTrue, hrightFalse⟩
  have hrightDiff :
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula (flipUniv on_ σ) skBase skCand rightLit
      hrightTrue hrightFalse
  rcases hpool.2.2 rightLit.var (flipUniv on_ σ) hrightDiff with
    ⟨hrightVar, hrightNoPathBase⟩
  have hrightEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hrightNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (σ on_)) rightLit := by
    have hrightNoPathLit :
        ¬ DeletePurePath s on_ (mkLit on_ (!((flipUniv on_ σ) on_)))
          rightLit := by
      rw [hrightEq]
      exact hrightNoPathBase
    simpa [flipUniv] using hrightNoPathLit
  exact ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
    hclauseFlipFalse, hnoCompl, hleftMem, hleftVar, hleftTrue,
    hleftFalse, hleftNoPath, hrightMem, hrightVar, hrightTrue,
    hrightFalse, hrightNoPath⟩

/-!
The same-clause package also contains the small universal-literal exclusions
from the TeX proof.  The two changed literals are existential variables, so
neither variable can be \(u\).  Moreover, if either \(u\)-literal occurred in
the false clause, that literal would be true on the corresponding universal
assignment, contradicting that the clause is false.
-/

theorem dependencyRemoval_sameClauseTwoPolarity_universalBoundaryFacts
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue σ skCand c.lits = false ∧
      s.formula.clauseValue (flipUniv on_ σ) skCand c.lits =
        false ∧
      (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ on_ ∧
      rightLit.var ≠ on_ ∧
      rightLit ≠ leftLit.negate ∧
      mkLit on_ (σ on_) ∉ c.lits.toList ∧
      mkLit on_ (!(σ on_)) ∉ c.lits.toList := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
      hclauseFlipFalse, hnoCompl, hleftMem, hleftVar,
      _hleftTrue, _hleftFalse, _hleftNoPath, hrightMem,
      hrightVar, _hrightTrue, _hrightFalse, _hrightNoPath⟩
  have hleftNeOn : leftLit.var ≠ on_ :=
    Nat.ne_of_gt (hgt leftLit.var hleftVar)
  have hrightNeOn : rightLit.var ≠ on_ :=
    Nat.ne_of_gt (hgt rightLit.var hrightVar)
  have hrightNeLeftNeg : rightLit ≠ leftLit.negate := by
    intro hEq
    exact (hnoCompl leftLit hleftMem) (by simpa [hEq] using hrightMem)
  have hstartSigmaNot :
      mkLit on_ (σ on_) ∉ c.lits.toList := by
    intro hmem
    have hfalse :
        s.formula.litValue σ skCand (mkLit on_ (σ on_)) = false :=
      dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula σ skCand c.lits hclauseFalse
        (mkLit on_ (σ on_)) hmem
    have htrue :
        s.formula.litValue σ skCand (mkLit on_ (σ on_)) = true :=
      dependencyRemoval_litValue_mkLit_universal_sigma_true
        s.formula on_ σ skCand hon_univ
    rw [htrue] at hfalse
    cases hfalse
  have hstartFlipNot :
      mkLit on_ (!(σ on_)) ∉ c.lits.toList := by
    intro hmem
    have hfalse :
        s.formula.litValue (flipUniv on_ σ) skCand
          (mkLit on_ (!(σ on_))) = false :=
      dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula (flipUniv on_ σ) skCand c.lits
        hclauseFlipFalse (mkLit on_ (!(σ on_))) hmem
    have htrue :
        s.formula.litValue (flipUniv on_ σ) skCand
          (mkLit on_ (!(σ on_))) = true :=
      dependencyRemoval_litValue_flipUniv_mkLit_universal_not_sigma_true
        s.formula on_ σ skCand hon_univ
    rw [htrue] at hfalse
    cases hfalse
  exact ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
    hclauseFlipFalse, hnoCompl, hleftMem, hrightMem, hleftVar,
    hrightVar, hleftNeOn, hrightNeOn, hrightNeLeftNeg,
    hstartSigmaNot, hstartFlipNot⟩

/-!
                The same false clause is used twice.  On the original side,
the left literal is true for \(f\) and false for \(f'\).  On the flipped side,
the right literal is true for \(f\) and false for \(f'\).  Because the clause
is false for \(f'\) on both sides, Lean can also read the crossed falsities:
the left literal is false for \(f'\) after the \(u\)-flip, and the right
literal is false for \(f'\) before the \(u\)-flip.

                These are the concrete Boolean facts used by the TeX argument
when it says the two same-clause literals are changed by the repair candidate.
-/

theorem dependencyRemoval_sameClauseTwoPolarity_crossFalseAndChanged
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue σ skCand c.lits = false ∧
      s.formula.clauseValue (flipUniv on_ σ) skCand c.lits =
        false ∧
      (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      s.formula.litValue σ skBase leftLit = true ∧
      s.formula.litValue σ skCand leftLit = false ∧
      s.formula.litValue (flipUniv on_ σ) skCand leftLit =
        false ∧
      s.formula.litValue (flipUniv on_ σ) skBase rightLit =
        true ∧
      s.formula.litValue (flipUniv on_ σ) skCand rightLit =
        false ∧
      s.formula.litValue σ skCand rightLit = false ∧
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var ∧
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var ∧
      leftLit.var ≠ on_ ∧
      rightLit.var ≠ on_ ∧
      rightLit ≠ leftLit.negate ∧
      mkLit on_ (σ on_) ∉ c.lits.toList ∧
      mkLit on_ (!(σ on_)) ∉ c.lits.toList := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
      hclauseFlipFalse, hnoCompl, hleftMem, hleftVar,
      hleftTrue, hleftFalse, _hleftNoPath, hrightMem,
      hrightVar, hrightTrue, hrightFalse, _hrightNoPath⟩
  have hleftNeOn : leftLit.var ≠ on_ :=
    Nat.ne_of_gt (hgt leftLit.var hleftVar)
  have hrightNeOn : rightLit.var ≠ on_ :=
    Nat.ne_of_gt (hgt rightLit.var hrightVar)
  have hrightNeLeftNeg : rightLit ≠ leftLit.negate := by
    intro hEq
    exact (hnoCompl leftLit hleftMem) (by simpa [hEq] using hrightMem)
  have hstartSigmaNot :
      mkLit on_ (σ on_) ∉ c.lits.toList := by
    intro hmem
    have hfalse :
        s.formula.litValue σ skCand (mkLit on_ (σ on_)) = false :=
      dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula σ skCand c.lits hclauseFalse
        (mkLit on_ (σ on_)) hmem
    have htrue :
        s.formula.litValue σ skCand (mkLit on_ (σ on_)) = true :=
      dependencyRemoval_litValue_mkLit_universal_sigma_true
        s.formula on_ σ skCand hon_univ
    rw [htrue] at hfalse
    cases hfalse
  have hstartFlipNot :
      mkLit on_ (!(σ on_)) ∉ c.lits.toList := by
    intro hmem
    have hfalse :
        s.formula.litValue (flipUniv on_ σ) skCand
          (mkLit on_ (!(σ on_))) = false :=
      dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula (flipUniv on_ σ) skCand c.lits
        hclauseFlipFalse (mkLit on_ (!(σ on_))) hmem
    have htrue :
        s.formula.litValue (flipUniv on_ σ) skCand
          (mkLit on_ (!(σ on_))) = true :=
      dependencyRemoval_litValue_flipUniv_mkLit_universal_not_sigma_true
        s.formula on_ σ skCand hon_univ
    rw [htrue] at hfalse
    cases hfalse
  have hleftFlipFalse :
      s.formula.litValue (flipUniv on_ σ) skCand leftLit = false :=
    dependencyRemoval_clauseValue_false_implies_lit_false
      s.formula (flipUniv on_ σ) skCand c.lits
      hclauseFlipFalse leftLit hleftMem
  have hrightSigmaFalse :
      s.formula.litValue σ skCand rightLit = false :=
    dependencyRemoval_clauseValue_false_implies_lit_false
      s.formula σ skCand c.lits hclauseFalse rightLit hrightMem
  have hleftChanged :
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand leftLit hleftTrue hleftFalse
  have hrightChanged :
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula (flipUniv on_ σ) skBase skCand rightLit
      hrightTrue hrightFalse
  exact ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
    hclauseFlipFalse, hnoCompl, hleftMem, hrightMem, hleftVar,
    hrightVar, hleftTrue, hleftFalse, hleftFlipFalse,
    hrightTrue, hrightFalse, hrightSigmaFalse, hleftChanged,
    hrightChanged, hleftNeOn, hrightNeOn, hrightNeLeftNeg,
    hstartSigmaNot, hstartFlipNot⟩

/-!
                The TeX proof freely switches between two equivalent ways of
saying that a literal is satisfied or falsified:

\[
  l \text{ is true under } f
  \quad\Longleftrightarrow\quad
  l = \operatorname{mkLit}(\operatorname{var}(l), f(\operatorname{var}(l))).
\]

For a false literal, the matching literal is its negation.  The next two Lean
lemmas make that conversion explicit, so later steps can refer to
\(l_y\), \(\bar l_y\), \(l_z\), and \(\bar l_z\) using concrete literals.
-/

theorem dependencyRemoval_literal_negate_var (l : Literal) :
    l.negate.var = l.var := by
  unfold Literal.negate Literal.var
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [← Nat.testBit_succ, Nat.testBit_xor]
  have h1 : Nat.testBit 1 (k + 1) = false := by
    rw [Bool.eq_false_iff]
    exact fun h =>
      Nat.succ_ne_zero k (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
  simp [h1]

theorem dependencyRemoval_literal_eq_mkLit_var_isPos (l : Literal) :
    l = mkLit l.var l.isPos := by
  cases l with
  | mk x =>
      unfold mkLit Literal.var Literal.isPos
      have hdecomp : x / 2 * 2 + x % 2 = x := by
        simpa [Nat.mul_comm] using Nat.div_add_mod x 2
      rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
      · simp [hmod]
        omega
      · simp [hmod]
        omega

theorem dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (hfalse : f.litValue σ sk l = false) :
    l.negate = mkLit l.var (f.varValue σ sk l.var) := by
  have hnegTrue : f.litValue σ sk l.negate = true := by
    rw [litValue_negate, hfalse]
    simp
  exact
    lit_eq_mkLit_varValue_of_var_and_true
      f l.var σ sk l.negate
      (by simp [dependencyRemoval_literal_negate_var])
      hnegTrue

theorem dependencyRemoval_litValue_true_varValue_eq_isPos
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (htrue : f.litValue σ sk l = true) :
    f.varValue σ sk l.var = l.isPos := by
  have hl : l = mkLit l.var l.isPos :=
    dependencyRemoval_literal_eq_mkLit_var_isPos l
  cases hpos : l.isPos
  · have hlFalse : l = mkLit l.var false := by
      simpa [hpos] using hl
    rw [hlFalse] at htrue
    rw [dependencyRemoval_litValue_mkLit_false] at htrue
    cases hv : f.varValue σ sk l.var
    · rfl
    · simp [hv] at htrue
  · have hlTrue : l = mkLit l.var true := by
      simpa [hpos] using hl
    rw [hlTrue] at htrue
    rw [dependencyRemoval_litValue_mkLit_true] at htrue
    simpa [hpos] using htrue

theorem dependencyRemoval_litValue_false_varValue_eq_not_isPos
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (hfalse : f.litValue σ sk l = false) :
    f.varValue σ sk l.var = !l.isPos := by
  have hl : l = mkLit l.var l.isPos :=
    dependencyRemoval_literal_eq_mkLit_var_isPos l
  cases hpos : l.isPos
  · have hlFalse : l = mkLit l.var false := by
      simpa [hpos] using hl
    rw [hlFalse] at hfalse
    rw [dependencyRemoval_litValue_mkLit_false] at hfalse
    cases hv : f.varValue σ sk l.var
    · simp [hv] at hfalse
    · rfl
  · have hlTrue : l = mkLit l.var true := by
      simpa [hpos] using hl
    rw [hlTrue] at hfalse
    rw [dependencyRemoval_litValue_mkLit_true] at hfalse
    simpa [hpos] using hfalse

theorem dependencyRemoval_varValue_eq_isPos_litValue_true
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (hval : f.varValue σ sk l.var = l.isPos) :
    f.litValue σ sk l = true := by
  unfold DQBF.litValue
  by_cases hpos : l.isPos <;> simp [hpos, hval]

theorem dependencyRemoval_varValue_eq_not_isPos_litValue_false
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (hval : f.varValue σ sk l.var = !l.isPos) :
    f.litValue σ sk l = false := by
  unfold DQBF.litValue
  by_cases hpos : l.isPos <;> simp [hpos, hval]

/-!
                Applying the conversion to the same-clause two-polarity
package gives the exact literal identities used by the TeX repair step.  The
left literal is the base value at \(\gamma\), while its negation is the
candidate value at \(\gamma\).  The right literal has the analogous identities
on \(\gamma^u\).
-/

theorem dependencyRemoval_sameClauseTwoPolarity_baseLiteralEqs
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) ∧
      leftLit.negate =
        mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) ∧
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) ∧
      rightLit.negate =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand rightLit.var) := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, _hclauseFalse,
      _hclauseFlipFalse, _hnoCompl, hleftMem, _hleftVar,
      hleftTrue, hleftFalse, _hleftNoPath, hrightMem,
      _hrightVar, hrightTrue, hrightFalse, _hrightNoPath⟩
  have hleftBaseEq :
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula leftLit.var σ skBase leftLit rfl hleftTrue
  have hleftCandNegEq :
      leftLit.negate =
        mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula σ skCand leftLit hleftFalse
  have hrightBaseEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hrightCandNegEq :
      rightLit.negate =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand rightLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula (flipUniv on_ σ) skCand rightLit hrightFalse
  exact ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem,
    hleftBaseEq, hleftCandNegEq, hrightBaseEq, hrightCandNegEq⟩

theorem dependencyRemoval_mkLit_same_var_pos_eq
    {v : Var} {p q : Bool} (h : mkLit v p = mkLit v q) :
    p = q := by
  cases p <;> cases q <;> simp [mkLit] at h ⊢ <;> omega

theorem dependencyRemoval_literal_eq_of_same_var_and_not_negate
    (l r : Literal)
    (hvar : l.var = r.var)
    (hnotNeg : r ≠ l.negate) :
    r = l := by
  rcases literal_eq_or_negate_of_same_var r l hvar.symm with hEq | hNeg
  · exact hEq
  · exact False.elim (hnotNeg hNeg)

theorem dependencyRemoval_sameClauseTwoPolarity_sameVar_noWitness_of_literals
    {s : CheckState} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    {c : Clause} {leftLit rightLit : Literal}
    (hnoCompl : ∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList)
    (hleftMem : leftLit ∈ c.lits.toList)
    (hrightMem : rightLit ∈ c.lits.toList)
    (hleftTrue : s.formula.litValue σ skBase leftLit = true)
    (hleftFalse : s.formula.litValue σ skCand leftLit = false)
    (hrightTrue :
      s.formula.litValue (flipUniv on_ σ) skBase rightLit = true)
    (hrightFalse :
      s.formula.litValue (flipUniv on_ σ) skCand rightLit = false)
    (hsameVar : leftLit.var = rightLit.var) :
    ¬ DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
      ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ := by
  have hrightNeLeftNeg : rightLit ≠ leftLit.negate := by
    intro hEq
    exact (hnoCompl leftLit hleftMem) (by simpa [hEq] using hrightMem)
  have hleftBaseEq :
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula leftLit.var σ skBase leftLit rfl hleftTrue
  have hleftCandNegEq :
      leftLit.negate =
        mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula σ skCand leftLit hleftFalse
  have hrightBaseEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hrightCandNegEq :
      rightLit.negate =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand rightLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula (flipUniv on_ σ) skCand rightLit hrightFalse
  have hrightEqLeft : rightLit = leftLit :=
    dependencyRemoval_literal_eq_of_same_var_and_not_negate
      leftLit rightLit hsameVar hrightNeLeftNeg
  subst rightLit
  have hbaseMk :
      mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) =
        mkLit leftLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase leftLit.var) :=
    hleftBaseEq.symm.trans hrightBaseEq
  have hcandMk :
      mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) =
        mkLit leftLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand leftLit.var) :=
    hleftCandNegEq.symm.trans hrightCandNegEq
  have hbase :
      s.formula.varValue σ skBase leftLit.var =
        s.formula.varValue (flipUniv on_ σ) skBase leftLit.var :=
    dependencyRemoval_mkLit_same_var_pos_eq hbaseMk
  have hcand :
      s.formula.varValue σ skCand leftLit.var =
        s.formula.varValue (flipUniv on_ σ) skCand leftLit.var :=
    dependencyRemoval_mkLit_same_var_pos_eq hcandMk
  constructor
  · intro hwit
    unfold DeleteDepWitness at hwit
    exact hwit hbase
  · intro hwit
    unfold DeleteDepWitness at hwit
    exact hwit hcand

/-!
                If the left and right changed literals in the same clause had
the same variable, then the no-complement condition forces them to be the same
literal.  The four literal identities above then say that the base Skolem
value is unchanged between \(\gamma\) and \(\gamma^u\), and the candidate value
is unchanged as well.  So same-variable two-polarity data cannot be a real
\(u\)-dependency witness.
-/

theorem dependencyRemoval_sameClauseTwoPolarity_sameVar_valueEqs
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      (leftLit.var = rightLit.var →
        s.formula.varValue σ skBase leftLit.var =
          s.formula.varValue (flipUniv on_ σ) skBase leftLit.var ∧
        s.formula.varValue σ skCand leftLit.var =
          s.formula.varValue (flipUniv on_ σ) skCand leftLit.var) := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, _hclauseFalse,
      _hclauseFlipFalse, hnoCompl, hleftMem, _hleftVar,
      hleftTrue, hleftFalse, _hleftNoPath, hrightMem,
      _hrightVar, hrightTrue, hrightFalse, _hrightNoPath⟩
  have hrightNeLeftNeg : rightLit ≠ leftLit.negate := by
    intro hEq
    exact (hnoCompl leftLit hleftMem) (by simpa [hEq] using hrightMem)
  have hleftBaseEq :
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula leftLit.var σ skBase leftLit rfl hleftTrue
  have hleftCandNegEq :
      leftLit.negate =
        mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula σ skCand leftLit hleftFalse
  have hrightBaseEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hrightCandNegEq :
      rightLit.negate =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand rightLit.var) :=
    dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
      s.formula (flipUniv on_ σ) skCand rightLit hrightFalse
  refine ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem, ?_⟩
  intro hsameVar
  have hrightEqLeft : rightLit = leftLit :=
    dependencyRemoval_literal_eq_of_same_var_and_not_negate
      leftLit rightLit hsameVar hrightNeLeftNeg
  subst rightLit
  have hbaseMk :
      mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) =
        mkLit leftLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase leftLit.var) :=
    hleftBaseEq.symm.trans hrightBaseEq
  have hcandMk :
      mkLit leftLit.var
          (s.formula.varValue σ skCand leftLit.var) =
        mkLit leftLit.var
          (s.formula.varValue (flipUniv on_ σ) skCand leftLit.var) :=
    hleftCandNegEq.symm.trans hrightCandNegEq
  exact ⟨dependencyRemoval_mkLit_same_var_pos_eq hbaseMk,
    dependencyRemoval_mkLit_same_var_pos_eq hcandMk⟩

theorem dependencyRemoval_sameClauseTwoPolarity_sameVar_noWitness
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      (leftLit.var = rightLit.var →
        ¬ DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
        ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ) := by
  rcases
      dependencyRemoval_sameClauseTwoPolarity_sameVar_valueEqs
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) hfailure with
    ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem,
      hstable⟩
  refine ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem, ?_⟩
  intro hsameVar
  rcases hstable hsameVar with ⟨hbase, hcand⟩
  constructor
  · intro hwit
    unfold DeleteDepWitness at hwit
    exact hwit hbase
  · intro hwit
    unfold DeleteDepWitness at hwit
    exact hwit hcand

/-!
                The path contradiction in the TeX proof is local to the same
clause.  The left changed literal already has no pure path from the opposite
\(u\)-side.  Since the whole clause is false for the current candidate, every
other literal in that clause is false on the same assignment.  Therefore a
pure path to the old value of the right changed variable would extend through
this clause back to the left changed literal, contradicting the left no-path
fact.
-/

theorem dependencyRemoval_sameClauseTwoPolarity_tailOldLiteralNoPurePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ rightLit.var ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit rightLit.var (!rightLit.isPos)) := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, hclauseFalse,
      _hclauseFlipFalse, hnoCompl, hleftMem, hleftVar,
      hleftTrue, hleftFalse, hleftNoPath, hrightMem,
      hrightVar, hrightTrue, hrightFalse, _hrightNoPath⟩
  rcases htracked with ⟨_hpool, hfoot, _hlive⟩
  have hleftChanged :
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand leftLit hleftTrue hleftFalse
  rcases hfoot leftLit.var σ hleftChanged with
    ⟨_hleftMemFoot, hleftBaseWitness, _hleftFiber⟩
  have hdistinct : leftLit.var ≠ rightLit.var := by
    intro hsameVar
    exact
      (dependencyRemoval_sameClauseTwoPolarity_sameVar_noWitness_of_literals
        (s := s) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (c := c)
        hnoCompl hleftMem hrightMem hleftTrue hleftFalse
        hrightTrue hrightFalse hsameVar).1 hleftBaseWitness
  have hleftMemMk :
      mkLit leftLit.var leftLit.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos leftLit]
    exact hleftMem
  have hrightMemMk :
      mkLit rightLit.var rightLit.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos rightLit]
    exact hrightMem
  have hleftNoPathMk :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit leftLit.var leftLit.isPos) := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos leftLit]
    exact hleftNoPath
  have hothers :
      ∀ l ∈ c.lits.toList, l ≠ mkLit leftLit.var leftLit.isPos →
        s.formula.litValue σ skCand l = false := by
    intro l hl _hne
    exact dependencyRemoval_clauseValue_false_implies_lit_false
      s.formula σ skCand c.lits hclauseFalse l hl
  have hrightOldNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit rightLit.var (!rightLit.isPos)) :=
    dependencyRemoval_sameClause_tailOldLiteralNoPurePath
      (s := s) (vars := vars) (on_ := on_)
      (of_ := leftLit.var) (nextOf := rightLit.var)
      (sk := skCand) (σ := σ) (cref := cref) (c := c)
      (pos := leftLit.isPos) (nextPos := rightLit.isPos)
      hon_univ hexi hcontains hleftVar hget hleftMemMk
      hleftNoPathMk (Ne.symm hdistinct) hrightMemMk hothers
  exact ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem,
    hleftVar, hrightVar, hdistinct, hrightOldNoPath⟩

/-!
                In the two-polarity branch, the two changed literals give two
real dependency witnesses of the original Skolem functions.  They cannot be
the same existential variable: if they were, the repair-pool footprint would
say the full dependency arguments at $\gamma$ and $\gamma^u$ are equal, but
those arguments differ exactly at $u$.

                The current candidate does not contain either witness.  This is
the Lean version of saying that the candidate has already removed those
witnesses from the pool of $u$-dependencies.
-/

theorem dependencyRemoval_twoPolarity_trackedWitnessFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ cref c leftLit rightLit,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ rightLit.var ∧
      DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
      ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ ∧
      DeleteDepWitness s.formula rightLit.var on_ skBase (flipUniv on_ σ) ∧
      ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
        (flipUniv on_ σ) := by
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, _hclauseFalse,
      _hclauseFlipFalse, _hnoCompl, hleftMem, hleftVar,
      hleftTrue, hleftFalse, _hleftNoPath, hrightMem,
      hrightVar, hrightTrue, hrightFalse, _hrightNoPath⟩
  rcases htracked with ⟨_hpool, hfoot, hlive⟩
  have hleftChanged :
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand leftLit hleftTrue hleftFalse
  have hrightChanged :
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula (flipUniv on_ σ) skBase skCand rightLit
      hrightTrue hrightFalse
  rcases hfoot leftLit.var σ hleftChanged with
    ⟨_hleftMem, hleftBaseWitness, hleftFiber⟩
  rcases hfoot rightLit.var (flipUniv on_ σ) hrightChanged with
    ⟨_hrightMem, hrightBaseWitness, _hrightFiber⟩
  have hdistinct : leftLit.var ≠ rightLit.var := by
    intro hsameVar
    have hrightChangedLeft :
        s.formula.varValue (flipUniv on_ σ) skCand leftLit.var ≠
          s.formula.varValue (flipUniv on_ σ) skBase leftLit.var := by
      simpa [hsameVar] using hrightChanged
    have hfullEq :
        fullDepArgs s.formula leftLit.var (flipUniv on_ σ) =
          fullDepArgs s.formula leftLit.var σ :=
      hleftFiber (flipUniv on_ σ)
        (deleteDepArgs_flipUniv s.formula leftLit.var on_ σ)
        hrightChangedLeft
    exact (fullDepArgs_flipUniv_ne_of_contains
      s.formula leftLit.var on_ σ (hcontains leftLit.var hleftVar))
      hfullEq
  have hleftNotLive :
      ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ := by
    intro hwit
    exact hleftChanged (hlive leftLit.var σ σ hleftVar hwit rfl)
  have hrightNotLive :
      ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
        (flipUniv on_ σ) := by
    intro hwit
    exact hrightChanged
      (hlive rightLit.var (flipUniv on_ σ) (flipUniv on_ σ)
        hrightVar hwit rfl)
  exact ⟨cref, c, leftLit, rightLit, hget, hleftMem, hrightMem,
    hleftVar, hrightVar, hdistinct, hleftBaseWitness, hleftNotLive,
    hrightBaseWitness, hrightNotLive⟩

/-!
                Now patch the two original witnesses: first the witness seen at
$\gamma$, then the witness seen at $\gamma^u$.  The previous theorem gives
that the two variables are distinct, so the second patch does not undo the
first one.  The result is still in the repair pool and has strictly fewer
$u$-dependency witnesses than the original Skolem functions.
-/

theorem dependencyRemoval_twoPolarity_twoPatchCandidate
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    ∃ skNext,
      FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
      deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skBase ∧
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase := by
  rcases hfailure with
    ⟨_cref, c, leftLit, rightLit, _hget, _hclauseFalse,
      _hclauseFlipFalse, hnoCompl, hleftMem, hleftVar,
      hleftTrue, hleftFalse, hleftNoPath, hrightMem,
      hrightVar, hrightTrue, hrightFalse, hrightNoPath⟩
  rcases htracked with ⟨_hpool, hfoot, _hlive⟩
  have hleftChanged :
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand leftLit hleftTrue hleftFalse
  have hrightChanged :
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula (flipUniv on_ σ) skBase skCand rightLit
      hrightTrue hrightFalse
  rcases hfoot leftLit.var σ hleftChanged with
    ⟨_hleftMem, hleftBaseWitness, _hleftFiber⟩
  rcases hfoot rightLit.var (flipUniv on_ σ) hrightChanged with
    ⟨_hrightMem, hrightBaseWitness, _hrightFiber⟩
  have hdistinct : leftLit.var ≠ rightLit.var := by
    intro hsameVar
    exact
      (dependencyRemoval_sameClauseTwoPolarity_sameVar_noWitness_of_literals
        (s := s) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (c := c)
        hnoCompl hleftMem hrightMem hleftTrue hleftFalse
        hrightTrue hrightFalse hsameVar).1 hleftBaseWitness
  have hleftBaseEq :
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula leftLit.var σ skBase leftLit rfl hleftTrue
  have hrightBaseEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hleftNoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit leftLit.var (s.formula.varValue σ skBase leftLit.var)) := by
    intro hpath
    rw [← hleftBaseEq] at hpath
    exact hleftNoPath hpath
  let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
  have htracked₁ :
      FlexibleRepairPoolTracked s vars on_ skBase sk₁ := by
    dsimp [sk₁]
    exact flexibleRepairPoolTracked_initial_patch
      (s := s) (vars := vars) (on_ := on_) (of_ := leftLit.var)
      (sk := skBase) (σSeed := σ)
      hexi hcontains hleftVar hleftBaseWitness hleftNoPathSeed
  have hrightWitness₁ :
      DeleteDepWitness s.formula rightLit.var on_ sk₁
        (flipUniv on_ σ) := by
    dsimp [sk₁]
    exact (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
      s.formula leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase (Ne.symm hdistinct)).2 hrightBaseWitness
  have hrightValueEq :
      s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var =
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var := by
    dsimp [sk₁]
    exact varValue_patchDeleteWitnessAt_eq_of_ne
      s.formula leftLit.var σ (flipUniv on_ σ) skBase
      (Ne.symm hdistinct)
  have hrightStartEq :
      mkLit on_ (!((flipUniv on_ σ) on_)) =
        mkLit on_ (σ on_) := by
    simp [flipUniv]
  have hrightEndEq :
      mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var) =
        rightLit := by
    rw [hrightValueEq]
    exact hrightBaseEq.symm
  have hrightNoPathSeed :
      ¬ DeletePurePath s on_
        (mkLit on_ (!((flipUniv on_ σ) on_)))
        (mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var)) := by
    intro hpath
    rw [hrightStartEq, hrightEndEq] at hpath
    exact hrightNoPath hpath
  let sk₂ :=
    patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ) sk₁
  have htracked₂ :
      FlexibleRepairPoolTracked s vars on_ skBase sk₂ := by
    dsimp [sk₂]
    exact flexibleRepairPoolTracked_patch_step
      (s := s) (vars := vars) (on_ := on_) (patched := rightLit.var)
      (skBase := skBase) (skCand := sk₁) (σSeed := flipUniv on_ σ)
      hexi hcontains htracked₁ hrightVar hrightWitness₁
      hrightNoPathSeed
  have hlt :
      deleteWitnessFiberCountSet s.formula vars on_ sk₂ <
        deleteWitnessFiberCountSet s.formula vars on_ skBase := by
    dsimp [sk₂, sk₁]
    exact deleteWitnessFiberCountSet_second_distinct_patch_lt
      s.formula vars leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase hleftVar (Ne.symm hdistinct)
      (hexi leftLit.var hleftVar) (hcontains leftLit.var hleftVar)
      hleftBaseWitness (hexi rightLit.var hrightVar)
      (hcontains rightLit.var hrightVar) hrightBaseWitness
  have hproper :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ sk₂ skBase := by
    dsimp [sk₂, sk₁]
    exact deleteWitnessFiberSetProperSubset_second_distinct_patch
      s.formula vars leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase hleftVar hrightVar hdistinct
      (hexi leftLit.var hleftVar) (hcontains leftLit.var hleftVar)
      hleftBaseWitness (hexi rightLit.var hrightVar)
      (hcontains rightLit.var hrightVar) hrightBaseWitness
  exact ⟨sk₂, htracked₂, hlt, hproper⟩

/-!
                If the two-patch Skolem set already satisfies every clause,
then the descent step is finished.  Otherwise some assignment still falsifies
the matrix.  Because the original Skolem functions satisfy the matrix, the
new false clause must contain a literal changed by one of the two patches.

                Lean records this remaining case as a concrete residual:
the same two witnesses have been removed, the new Skolem set is still in the
repair pool, and the false assignment identifies which patch-fiber still has
to be explained by the next part of the descent.
-/

theorem dependencyRemoval_twoPolarity_twoPatch_model_or_concreteResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfailure :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ) :
    (∃ sk',
      (∀ τ, s.clauses.matrixValue s.formula τ sk' = true) ∧
      deleteWitnessFiberCountSet s.formula vars on_ sk' <
        deleteWitnessFiberCountSet s.formula vars on_ skBase) ∨
      ∃ skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skBase ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext ∧
        (deleteWitnessFiberCountSet s.formula vars on_ skCand <
            deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
          DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand) ∧
        DependencyRemovalExactTwoPatchResidual
          s vars on_ skBase skCand skNext σ := by
  classical
  rcases hfailure with
    ⟨cref, c, leftLit, rightLit, hget, _hclauseFalse,
      _hclauseFlipFalse, hnoCompl, hleftMem, hleftVar,
      hleftTrue, hleftFalse, hleftNoPath, hrightMem,
      hrightVar, hrightTrue, hrightFalse, hrightNoPath⟩
  have htrackedOrig :
      FlexibleRepairPoolTracked s vars on_ skBase skCand := htracked
  rcases htracked with ⟨_hpool, hfoot, hlive⟩
  have hleftChanged :
      s.formula.varValue σ skCand leftLit.var ≠
        s.formula.varValue σ skBase leftLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula σ skBase skCand leftLit hleftTrue hleftFalse
  have hrightChanged :
      s.formula.varValue (flipUniv on_ σ) skCand rightLit.var ≠
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula (flipUniv on_ σ) skBase skCand rightLit
      hrightTrue hrightFalse
  rcases hfoot leftLit.var σ hleftChanged with
    ⟨_hleftMem, hleftBaseWitness, _hleftFiber⟩
  rcases hfoot rightLit.var (flipUniv on_ σ) hrightChanged with
    ⟨_hrightMem, hrightBaseWitness, _hrightFiber⟩
  have hdistinct : leftLit.var ≠ rightLit.var := by
    intro hsameVar
    exact
      (dependencyRemoval_sameClauseTwoPolarity_sameVar_noWitness_of_literals
        (s := s) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (c := c)
        hnoCompl hleftMem hrightMem hleftTrue hleftFalse
        hrightTrue hrightFalse hsameVar).1 hleftBaseWitness
  have hleftNotLive :
      ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ := by
    intro hwit
    exact hleftChanged (hlive leftLit.var σ σ hleftVar hwit rfl)
  have hrightNotLive :
      ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
        (flipUniv on_ σ) := by
    intro hwit
    exact hrightChanged
      (hlive rightLit.var (flipUniv on_ σ) (flipUniv on_ σ)
        hrightVar hwit rfl)
  have hleftBaseEq :
      leftLit =
        mkLit leftLit.var
          (s.formula.varValue σ skBase leftLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula leftLit.var σ skBase leftLit rfl hleftTrue
  have hrightBaseEq :
      rightLit =
        mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) skBase rightLit.var) :=
    lit_eq_mkLit_varValue_of_var_and_true
      s.formula rightLit.var (flipUniv on_ σ) skBase rightLit
      rfl hrightTrue
  have hleftNoPathSeed :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
        (mkLit leftLit.var (s.formula.varValue σ skBase leftLit.var)) := by
    intro hpath
    rw [← hleftBaseEq] at hpath
    exact hleftNoPath hpath
  let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
  have htracked₁ :
      FlexibleRepairPoolTracked s vars on_ skBase sk₁ := by
    dsimp [sk₁]
    exact flexibleRepairPoolTracked_initial_patch
      (s := s) (vars := vars) (on_ := on_) (of_ := leftLit.var)
      (sk := skBase) (σSeed := σ)
      hexi hcontains hleftVar hleftBaseWitness hleftNoPathSeed
  have hrightWitness₁ :
      DeleteDepWitness s.formula rightLit.var on_ sk₁
        (flipUniv on_ σ) := by
    dsimp [sk₁]
    exact (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
      s.formula leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase (Ne.symm hdistinct)).2 hrightBaseWitness
  have hrightValueEq :
      s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var =
        s.formula.varValue (flipUniv on_ σ) skBase rightLit.var := by
    dsimp [sk₁]
    exact varValue_patchDeleteWitnessAt_eq_of_ne
      s.formula leftLit.var σ (flipUniv on_ σ) skBase
      (Ne.symm hdistinct)
  have hrightStartEq :
      mkLit on_ (!((flipUniv on_ σ) on_)) =
        mkLit on_ (σ on_) := by
    simp [flipUniv]
  have hrightEndEq :
      mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var) =
        rightLit := by
    rw [hrightValueEq]
    exact hrightBaseEq.symm
  have hrightNoPathSeed :
      ¬ DeletePurePath s on_
        (mkLit on_ (!((flipUniv on_ σ) on_)))
        (mkLit rightLit.var
          (s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var)) := by
    intro hpath
    rw [hrightStartEq, hrightEndEq] at hpath
    exact hrightNoPath hpath
  let sk₂ :=
    patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ) sk₁
  have htracked₂ :
      FlexibleRepairPoolTracked s vars on_ skBase sk₂ := by
    dsimp [sk₂]
    exact flexibleRepairPoolTracked_patch_step
      (s := s) (vars := vars) (on_ := on_) (patched := rightLit.var)
      (skBase := skBase) (skCand := sk₁) (σSeed := flipUniv on_ σ)
      hexi hcontains htracked₁ hrightVar hrightWitness₁
      hrightNoPathSeed
  have hlt₂ :
      deleteWitnessFiberCountSet s.formula vars on_ sk₂ <
        deleteWitnessFiberCountSet s.formula vars on_ skBase := by
    dsimp [sk₂, sk₁]
    exact deleteWitnessFiberCountSet_second_distinct_patch_lt
      s.formula vars leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase hleftVar (Ne.symm hdistinct)
      (hexi leftLit.var hleftVar) (hcontains leftLit.var hleftVar)
      hleftBaseWitness (hexi rightLit.var hrightVar)
      (hcontains rightLit.var hrightVar) hrightBaseWitness
  have hproper₂ :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ sk₂ skBase := by
    dsimp [sk₂, sk₁]
    exact deleteWitnessFiberSetProperSubset_second_distinct_patch
      s.formula vars leftLit.var rightLit.var on_ σ (flipUniv on_ σ)
      skBase hleftVar hrightVar hdistinct
      (hexi leftLit.var hleftVar) (hcontains leftLit.var hleftVar)
      hleftBaseWitness (hexi rightLit.var hrightVar)
      (hcontains rightLit.var hrightVar) hrightBaseWitness
  have hsubsetCand₂ :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand sk₂ := by
    rcases flexibleRepairSameClauseTwoPatchCandidate_current_subset_core
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (leftLit := leftLit)
        (rightLit := rightLit)
        hexi hcontains htrackedOrig hleftVar hleftTrue hleftFalse
        hrightVar hrightTrue hrightFalse with
      ⟨_hdistinct, hsubset⟩
    simpa [sk₂, sk₁] using hsubset
  have hsplitCand₂ :
      deleteWitnessFiberCountSet s.formula vars on_ skCand <
          deleteWitnessFiberCountSet s.formula vars on_ sk₂ ∨
        DeleteWitnessFiberSetSubset s.formula vars on_ sk₂ skCand := by
    rcases flexibleRepairSameClauseTwoPatchCandidate_current_subset_split_core
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ) (leftLit := leftLit)
        (rightLit := rightLit)
        hexi hcontains htrackedOrig hleftVar hleftTrue hleftFalse
        hrightVar hrightTrue hrightFalse with
      ⟨_hdistinct, hsplit⟩
    simpa [sk₂, sk₁] using hsplit
  by_cases hfail :
      ∃ τ, s.clauses.matrixValue s.formula τ sk₂ = false
  · right
    rcases hfail with ⟨τ, hfalse⟩
    have hchanged :
        TwoPatchChangedLit s.formula s.clauses leftLit.var
          rightLit.var σ (flipUniv on_ σ) τ skBase :=
      matrixValue_two_patch_false_implies_changed_lit_in_patched_vars
        s.formula s.clauses leftLit.var rightLit.var σ
        (flipUniv on_ σ) τ skBase hallBase (by
          simpa [sk₂, sk₁] using hfalse)
    have hcases :
        PatchChangedLit s.formula s.clauses leftLit.var σ τ skBase ∨
          PatchChangedLit s.formula s.clauses rightLit.var
            (flipUniv on_ σ) τ sk₁ :=
      twoPatchChangedLit_cases
        s.formula s.clauses (Ne.symm hdistinct) hchanged
    have hremoved :
        (PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
            skBase ∧
          ¬ DeleteDepWitness s.formula leftLit.var on_ sk₂ τ) ∨
        (PatchChangedFiber s.formula s.clauses rightLit.var on_
            (flipUniv on_ σ) τ sk₁ ∧
          ¬ DeleteDepWitness s.formula rightLit.var on_ sk₂ τ) := by
      rcases hcases with hfirst | hsecond
      · left
        have hfiber :
            PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
              skBase :=
          patchChangedLit_implies_fiber
            s.formula s.clauses (hexi leftLit.var hleftVar)
            (hcontains leftLit.var hleftVar) hfirst
        have hnoFirst :
            ¬ DeleteDepWitness s.formula leftLit.var on_
              (patchDeleteWitnessAt s.formula leftLit.var σ skBase) τ :=
          patchChangedFiber_removed_by_patch
            s.formula s.clauses (hexi leftLit.var hleftVar)
            (hcontains leftLit.var hleftVar) hleftBaseWitness hfiber
        refine ⟨hfiber, ?_⟩
        intro hdouble
        have hfirstWitness :
            DeleteDepWitness s.formula leftLit.var on_
              (patchDeleteWitnessAt s.formula leftLit.var σ skBase) τ :=
          (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
            s.formula rightLit.var leftLit.var on_ (flipUniv on_ σ) τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase)
            hdistinct).1 (by simpa [sk₂, sk₁] using hdouble)
        exact hnoFirst hfirstWitness
      · right
        have hfiber :
            PatchChangedFiber s.formula s.clauses rightLit.var on_
              (flipUniv on_ σ) τ sk₁ :=
          patchChangedLit_implies_fiber
            s.formula s.clauses (hexi rightLit.var hrightVar)
            (hcontains rightLit.var hrightVar) hsecond
        have hnoSecond :
            ¬ DeleteDepWitness s.formula rightLit.var on_
              (patchDeleteWitnessAt s.formula rightLit.var
                (flipUniv on_ σ) sk₁) τ :=
          patchChangedFiber_removed_by_patch
            s.formula s.clauses (hexi rightLit.var hrightVar)
            (hcontains rightLit.var hrightVar) hrightWitness₁ hfiber
        refine ⟨hfiber, ?_⟩
        simpa [sk₂] using hnoSecond
    have hexact :
        DependencyRemovalExactTwoPatchResidual
          s vars on_ skBase skCand sk₂ σ := by
      refine ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
        hrightMem, hleftVar, hrightVar, hdistinct, hleftBaseWitness,
        hleftNotLive, hrightBaseWitness, hrightNotLive,
        hleftNoPathSeed, hrightNoPathSeed, ?_, ?_, ?_, hremoved⟩
      · simpa [sk₂, sk₁] using hfalse
      · rfl
      · dsimp [sk₂, sk₁]
        exact dependencyRemoval_twoPatch_changedClause_from_false
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (leftLit := leftLit) (rightLit := rightLit) (σ := σ) (τ := τ)
          hexi hcontains hleftVar hrightVar hdistinct hallBase
          (by simpa [sk₂, sk₁] using hfalse)
    exact ⟨sk₂, htracked₂, hlt₂, hproper₂, hsubsetCand₂,
      hsplitCand₂, hexact⟩
  · left
    refine ⟨sk₂, ?_, hlt₂⟩
    intro τ
    cases hval : s.clauses.matrixValue s.formula τ sk₂ with
    | false => exact False.elim (hfail ⟨τ, hval⟩)
    | true => rfl

/-!
                The same-clause branch is now a local continuation step.  If
the two-patch candidate is a model, we are done.  If it is still false and has
strictly fewer current witnesses, it is the next induction candidate.  The
only remaining case is the residual where the two-patch candidate is not
smaller than the current candidate by the plain witness count; that case is
isolated as a residual handler that returns the same local continuation shape.
-/

theorem dependencyRemoval_sameClauseFailure_currentStrictStep_or_outcome_of_residualHandler
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hproperCand :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false)
    (hfailure :
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand := by
  classical
  have htwo :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ :=
    dependencyRemoval_sameClauseFailure_twoPolarity
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ) htracked.1 hallBase hfailure
  rcases
      dependencyRemoval_twoPolarity_twoPatch_model_or_concreteResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hexi hcontains hallBase htracked htwo with
    houtcome | hresidual
  · exact Or.inl (Or.inl houtcome)
  · rcases hresidual with
      ⟨skNext, htrackedNext, hltNextBase, hproperNext,
        hsubsetCandNext, hsplitCandNext, hexact⟩
    by_cases hltCurrent :
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCand
    · exact Or.inr
        ⟨skNext, htrackedNext, hltCurrent⟩
    · exact
        hhandler hallBase htracked hfalse htwo hproperCand
          htrackedNext hltNextBase hproperNext hsubsetCandNext
          hsplitCandNext hltCurrent hexact

/-!
The TeX proof measures progress by the finite set of remaining dependency
witnesses.  The Lean residual split shows why the plain count is not always
the whole story: the two-patch candidate may be proper-smaller than the
original \(f\), but not smaller than the current \(f'\) by that count.

The following rank form keeps the finite-descent paragraph honest.  If a
nondecreasing residual does not lower the witness count, the proof may supply
some stronger natural-valued rank that does decrease.  The induction theorem
below is the same "eventually terminates" argument, but over that rank.
-/

abbrev DependencyRemovalSameClauseRankedRestart
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseFlipFailure s vars on_ skBase skCand σ →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank skNext < rank skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

abbrev DependencyRemovalSameClauseConcreteNondecreasingResidualRankDecrease
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    (deleteWitnessFiberCountSet s.formula vars on_ skCand <
        deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand) →
    ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    rank skNext < rank skCand

abbrev DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    (deleteWitnessFiberCountSet s.formula vars on_ skCand <
        deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand) →
    ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

theorem dependencyRemoval_sameClauseRankedRestart_of_concreteResidualRank
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresRank :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankDecrease
        s vars on_ rank) :
    DependencyRemovalSameClauseRankedRestart s vars on_ rank := by
  intro skBase skCand σ hallBase htracked hproperCand hfalse hfailure
  have htwo :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ :=
    dependencyRemoval_sameClauseFailure_twoPolarity
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ) htracked.1 hallBase hfailure
  rcases
      dependencyRemoval_twoPolarity_twoPatch_model_or_concreteResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hexi hcontains hallBase htracked htwo with
    houtcome | hresidual
  · exact Or.inl (Or.inl houtcome)
  · rcases hresidual with
      ⟨skNext, htrackedNext, hltNextBase, hproperNext,
        hsubsetCandNext, hsplitCandNext, hexact⟩
    have hfalseNext :
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false :=
      dependencyRemoval_exactTwoPatchResidual_falseMatrix
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexact
    by_cases hltCurrent :
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCand
    · exact Or.inr
        ⟨skNext, htrackedNext, hproperNext, hrank_count hltCurrent,
          hfalseNext⟩
    · exact Or.inr
        ⟨skNext, htrackedNext, hproperNext,
          hresRank hallBase htracked hfalse htwo hproperCand
            htrackedNext hltNextBase hproperNext hsubsetCandNext
            hsplitCandNext hltCurrent hexact,
          hfalseNext⟩

theorem dependencyRemoval_sameClauseRankedRestart_of_concreteResidualRankProgress
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresProgress :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
        s vars on_ rank) :
    DependencyRemovalSameClauseRankedRestart s vars on_ rank := by
  intro skBase skCand σ hallBase htracked hproperCand hfalse hfailure
  let handleLocal :
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand →
      DependencyRemovalDescentOutcome s vars on_ skBase ∨
        ∃ skNext,
          FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
          DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
          rank skNext < rank skCand ∧
          ∃ τ, s.clauses.matrixValue s.formula τ skNext = false := by
    intro hlocal
    rcases hlocal with houtcome | hstrict
    · exact Or.inl houtcome
    · rcases hstrict with ⟨skStrict, htrackedStrict, hltStrict⟩
      by_cases hfailStrict :
          ∃ ρ, s.clauses.matrixValue s.formula ρ skStrict = false
      · rcases hfailStrict with ⟨ρ, hfalseStrict⟩
        have hproperStrict :
            DeleteWitnessFiberSetProperSubset
              s.formula vars on_ skStrict skBase :=
          dependencyRemoval_trackedFalseCandidate_hasProperSubset
            (s := s) (vars := vars) (on_ := on_)
            (skBase := skBase) (skCand := skStrict) (σ := ρ)
            hallBase htrackedStrict hfalseStrict
        exact Or.inr
          ⟨skStrict, htrackedStrict, hproperStrict,
            hrank_count hltStrict, ρ, hfalseStrict⟩
      · exact Or.inl
          (Or.inl ⟨skStrict,
            (by
              intro ρ
              cases hval :
                  s.clauses.matrixValue s.formula ρ skStrict with
              | false => exact False.elim (hfailStrict ⟨ρ, hval⟩)
              | true => rfl),
            htrackedStrict.1.1⟩)
  have htwo :
      FlexibleRepairSameClauseTwoPolarityFailure
        s vars on_ skBase skCand σ :=
    dependencyRemoval_sameClauseFailure_twoPolarity
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ) htracked.1 hallBase hfailure
  rcases
      dependencyRemoval_twoPolarity_twoPatch_model_or_concreteResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hexi hcontains hallBase htracked htwo with
    houtcome | hresidual
  · exact Or.inl (Or.inl houtcome)
  · rcases hresidual with
      ⟨skNext, htrackedNext, hltNextBase, hproperNext,
        hsubsetCandNext, hsplitCandNext, hexact⟩
    have hfalseNext :
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false :=
      dependencyRemoval_exactTwoPatchResidual_falseMatrix
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexact
    by_cases hltCurrent :
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCand
    · exact Or.inr
        ⟨skNext, htrackedNext, hproperNext, hrank_count hltCurrent,
          hfalseNext⟩
    · rcases
        hresProgress hallBase htracked hfalse htwo hproperCand
          htrackedNext hltNextBase hproperNext hsubsetCandNext
          hsplitCandNext hltCurrent hexact with
        hlocal | hrank
      · exact handleLocal hlocal
      · exact Or.inr
          ⟨skNext, htrackedNext, hproperNext, hrank, hfalseNext⟩

theorem dependencyRemoval_rankedFalseStep_of_sameClauseRankedRestart
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hsameRank : DependencyRemovalSameClauseRankedRestart s vars on_ rank) :
    DependencyRemovalRankedFalseStep s vars on_ rank := by
  classical
  intro skBase skCand σ hallBase htracked hproper hfalse
  let handleStrict :
      FlexibleRepairTrackedStrictStep s vars on_ skBase skCand →
      DependencyRemovalDescentOutcome s vars on_ skBase ∨
        ∃ skNext,
          FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
          DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
          rank skNext < rank skCand ∧
          ∃ τ, s.clauses.matrixValue s.formula τ skNext = false := by
    intro hstrict
    rcases hstrict with ⟨skNext, htrackedNext, hltNext⟩
    by_cases hfailNext :
        ∃ ρ, s.clauses.matrixValue s.formula ρ skNext = false
    · rcases hfailNext with ⟨ρ, hfalseNext⟩
      have hproperNext :
          DeleteWitnessFiberSetProperSubset
            s.formula vars on_ skNext skBase :=
        dependencyRemoval_trackedFalseCandidate_hasProperSubset
          (s := s) (vars := vars) (on_ := on_)
          (skBase := skBase) (skCand := skNext) (σ := ρ)
          hallBase htrackedNext hfalseNext
      exact Or.inr
        ⟨skNext, htrackedNext, hproperNext, hrank_count hltNext,
          ρ, hfalseNext⟩
    · exact Or.inl
        (Or.inl ⟨skNext,
          (by
            intro ρ
            cases hval :
                s.clauses.matrixValue s.formula ρ skNext with
            | false => exact False.elim (hfailNext ⟨ρ, hval⟩)
            | true => rfl),
          htrackedNext.1.1⟩)
  rcases
      dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_sameClauseFailure
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
        (on_ := on_) (skBase := skBase) (skCand := skCand) (σ := σ)
        hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
        htracked hallBase hfalse with
    hstrict | hsameClause
  · exact handleStrict hstrict
  · exact hsameRank hallBase htracked hproper hfalse hsameClause

theorem dependencyRemoval_trackedFalseRestart_of_sameClauseResidualRank
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresRank :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankDecrease
        s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_rankedFalseStep
    (s := s) (vars := vars) (on_ := on_) rank
    (dependencyRemoval_rankedFalseStep_of_sameClauseRankedRestart
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count
      (dependencyRemoval_sameClauseRankedRestart_of_concreteResidualRank
        (s := s) (vars := vars) (on_ := on_) rank hexi hcontains
        hrank_count hresRank))

theorem dependencyRemoval_trackedFalseRestart_of_sameClauseResidualRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresProgress :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
        s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_rankedFalseStep
    (s := s) (vars := vars) (on_ := on_) rank
    (dependencyRemoval_rankedFalseStep_of_sameClauseRankedRestart
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count
      (dependencyRemoval_sameClauseRankedRestart_of_concreteResidualRankProgress
        (s := s) (vars := vars) (on_ := on_) rank hexi hcontains
        hrank_count hresProgress))

/-!
This names the one equivalent-footprint branch still left open here.  The
two-patch candidate has a false clause whose changed literal has no pure path,
but another literal in the same clause has the pure path that blocks the
direct patch from the current candidate.
-/

abbrev DependencyRemovalEquivalentFootprintPathObstruction
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var (s.formula.varValue τ skCand flipLit.var))

/-!
The equivalent-footprint obstruction is actually impossible.  The live witness
for the flip literal is present in both tracked candidates, so both candidates
agree with the original Skolem functions on that variable.  Hence the path
endpoint written with the current candidate is the same old literal seen in
the residual false clause.  The same-clause tail lemma then contradicts the
changed literal's missing pure path.
-/

theorem dependencyRemoval_equivalentFootprintPathObstruction_false
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hobs :
      DependencyRemovalEquivalentFootprintPathObstruction
        s vars on_ skCand skNext) :
    False := by
  classical
  rcases hobs with
    ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
      hchangedMem, hchangedVar, hchangedFalse, hchangedFlipFalse,
      hchangedNoPath, hnoCompl, hflipMem, hflipFalse, hflipTrue,
      hwitCand, hexiFlip, hcontainsFlip, hpath⟩
  have hflipVar : flipLit.var ∈ vars.toList :=
    hclosed flipLit.var hexiFlip hcontainsFlip
  have hwitNext :
      DeleteDepWitness s.formula flipLit.var on_ skNext τ :=
    Classical.byContradiction (fun hnotNext =>
      (deleteWitnessFiberSetSubset_not_deleteDepWitness
        (f := s.formula) (vars := vars) (on_ := on_)
        (of_ := flipLit.var) (skSmall := skCand)
        (skBig := skNext) (σ := τ)
        hexiFlip hsubsetCandNext hflipVar hnotNext) hwitCand)
  have hCandBase :
      s.formula.varValue τ skCand flipLit.var =
          s.formula.varValue τ skBase flipLit.var ∧
        s.formula.varValue (flipUniv on_ τ) skCand flipLit.var =
          s.formula.varValue (flipUniv on_ τ) skBase flipLit.var :=
    dependencyRemoval_liveCandidateWitness_agreesWithBase
      (s := s) (vars := vars) (on_ := on_)
      (of_ := flipLit.var) (skBase := skBase)
      (skCand := skCand) (σ := τ)
      htracked hflipVar hwitCand
  have hNextBase :
      s.formula.varValue τ skNext flipLit.var =
          s.formula.varValue τ skBase flipLit.var ∧
        s.formula.varValue (flipUniv on_ τ) skNext flipLit.var =
          s.formula.varValue (flipUniv on_ τ) skBase flipLit.var :=
    dependencyRemoval_liveCandidateWitness_agreesWithBase
      (s := s) (vars := vars) (on_ := on_)
      (of_ := flipLit.var) (skBase := skBase)
      (skCand := skNext) (σ := τ)
      htrackedNext hflipVar hwitNext
  have hvalueCandNext :
      s.formula.varValue τ skCand flipLit.var =
        s.formula.varValue τ skNext flipLit.var :=
    hCandBase.1.trans hNextBase.1.symm
  have hnextValuePol :
      s.formula.varValue τ skNext flipLit.var = !flipLit.isPos :=
    dependencyRemoval_litValue_false_varValue_eq_not_isPos
      s.formula τ skNext flipLit hflipFalse
  have hpathTarget :
      mkLit flipLit.var (s.formula.varValue τ skCand flipLit.var) =
        mkLit flipLit.var (!flipLit.isPos) := by
    rw [hvalueCandNext, hnextValuePol]
  have hdistinct : flipLit.var ≠ changed.var := by
    intro hsame
    have hnotNeg : flipLit ≠ changed.negate := by
      intro hEq
      exact (hnoCompl changed hchangedMem) (by simpa [hEq] using hflipMem)
    have hflipEqChanged : flipLit = changed :=
      dependencyRemoval_literal_eq_of_same_var_and_not_negate
        changed flipLit hsame.symm hnotNeg
    have htrueChanged :
        s.formula.litValue (flipUniv on_ τ) skNext changed = true := by
      simpa [hflipEqChanged] using hflipTrue
    rw [hchangedFlipFalse] at htrueChanged
    cases htrueChanged
  have hchangedMemMk :
      mkLit changed.var changed.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
    exact hchangedMem
  have hflipMemMk :
      mkLit flipLit.var flipLit.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos flipLit]
    exact hflipMem
  have hchangedNoPathMk :
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit changed.var changed.isPos) := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
    exact hchangedNoPath
  have hothers :
      ∀ l ∈ c.lits.toList, l ≠ mkLit changed.var changed.isPos →
        s.formula.litValue τ skNext l = false := by
    intro l hl _hne
    exact dependencyRemoval_clauseValue_false_implies_lit_false
      s.formula τ skNext c.lits hclauseFalse l hl
  have htailNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit flipLit.var (!flipLit.isPos)) :=
    dependencyRemoval_sameClause_tailOldLiteralNoPurePath
      (s := s) (vars := vars) (on_ := on_)
      (of_ := changed.var) (nextOf := flipLit.var)
      (sk := skNext) (σ := τ) (cref := cref) (c := c)
      (pos := changed.isPos) (nextPos := flipLit.isPos)
      hon_univ hexi hcontains hchangedVar hget hchangedMemMk
      hchangedNoPathMk hdistinct hflipMemMk hothers
  exact htailNoPath (by simpa [hpathTarget] using hpath)

/-!
The proper-growth branch has one additional residual shape.  The two-patch
candidate may contain a dependency witness that the current candidate does not
contain.  The following name keeps exactly the data for that case visible: the
false residual clause, the changed literal in that clause, and the newly
created witness together with the current candidate's old-literal observation.
-/

abbrev DependencyRemovalProperGrowthNewWitnessObstruction
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ σSide,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
    s.formula.varValue σSide skCand flipLit.var ≠
      s.formula.varValue σSide skBase flipLit.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) = false ∧
    ∀ ρ,
      deleteDepArgs s.formula flipLit.var on_ ρ =
        deleteDepArgs s.formula flipLit.var on_ σSide →
      s.formula.varValue ρ skCand flipLit.var ≠
        s.formula.varValue ρ skBase flipLit.var →
      fullDepArgs s.formula flipLit.var ρ =
        fullDepArgs s.formula flipLit.var σSide

/-!
The new-witness obstruction also tells us what happened to the concrete
residual clause.  If the current candidate changed the original value on the
residual assignment itself, the newly found literal is already true for the
current candidate, so that residual clause is not a current false clause.  If
the change was on the flipped side, then the new literal is false for the
current candidate on both sides, and the same-clause tail argument supplies
the missing pure-path side condition for its current value.
-/

abbrev DependencyRemovalProperGrowthCurrentTrueObservedResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ σSide,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
    s.formula.varValue σSide skCand flipLit.var ≠
      s.formula.varValue σSide skBase flipLit.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) = false ∧
    (∀ ρ,
      deleteDepArgs s.formula flipLit.var on_ ρ =
        deleteDepArgs s.formula flipLit.var on_ σSide →
      s.formula.varValue ρ skCand flipLit.var ≠
        s.formula.varValue ρ skBase flipLit.var →
      fullDepArgs s.formula flipLit.var ρ =
        fullDepArgs s.formula flipLit.var σSide) ∧
    s.formula.litValue τ skCand flipLit = true ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = true

/-!
In the TeX proof, the next repair literal is not just the newly observed
`flipLit`.  The residual clause is false for the two-patch candidate but true
for the current candidate, so there is a concrete clause literal which is true
for `skCand` and false for `skNext`.  The tracked-pool invariant says that
this live literal is still in the dependency-removal pool and that the
original Skolem functions had a \(u\)-witness for it.
-/

abbrev DependencyRemovalProperGrowthCurrentTrueLiveResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit liveLit τ σSide,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
    s.formula.varValue σSide skCand flipLit.var ≠
      s.formula.varValue σSide skBase flipLit.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) = false ∧
    (∀ ρ,
      deleteDepArgs s.formula flipLit.var on_ ρ =
        deleteDepArgs s.formula flipLit.var on_ σSide →
      s.formula.varValue ρ skCand flipLit.var ≠
        s.formula.varValue ρ skBase flipLit.var →
      fullDepArgs s.formula flipLit.var ρ =
        fullDepArgs s.formula flipLit.var σSide) ∧
    s.formula.litValue τ skCand flipLit = true ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = true ∧
    liveLit ∈ c.lits.toList ∧
    liveLit.var ∈ vars.toList ∧
    DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
    s.formula.litValue τ skCand liveLit = true ∧
    s.formula.litValue τ skNext liveLit = false

theorem dependencyRemoval_properGrowthCurrentTrueObserved_liveResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hres :
      DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext) :
    DependencyRemovalProperGrowthCurrentTrueLiveResidual
      s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨cref, c, changed, flipLit, τ, σSide, hget,
      hnextFalse, hcurrentTrue, hchangedMem, hchangedVar,
      hchangedTrue, hchangedNextFalse, hchangedNextFlipFalse,
      hchangedNoPath, hnoCompl, hflipMem, hflipVar,
      hflipNextFalse, hflipNextTrue, hwitNext, hnotCand,
      hexiFlip, hcontainsFlip, hside, hbaseSide, hnotSide,
      hchangedCurrent, hnoPathCurrent, holdFalse, hfiber,
      hflipCandTrue, hflipCandFlipTrue⟩
  rcases clauseValue_true_false_implies_exists_true_false_lit
      s.formula τ skCand skNext c.lits hcurrentTrue hnextFalse with
    ⟨liveLit, hliveMem, hliveCandTrue, hliveNextFalse⟩
  have hdiffNextCand :
      s.formula.varValue τ skNext liveLit.var ≠
        s.formula.varValue τ skCand liveLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula τ skCand skNext liveLit hliveCandTrue hliveNextFalse
  have hliveBaseInfo :
      liveLit.var ∈ vars.toList ∧
        DeleteDepWitness s.formula liveLit.var on_ skBase τ := by
    by_cases hnextBase :
        s.formula.varValue τ skNext liveLit.var =
          s.formula.varValue τ skBase liveLit.var
    · have hcandBase :
          s.formula.varValue τ skCand liveLit.var ≠
            s.formula.varValue τ skBase liveLit.var := by
        intro hcandBase
        exact hdiffNextCand (hnextBase.trans hcandBase.symm)
      rcases htracked.2.1 liveLit.var τ hcandBase with
        ⟨hliveVar, hwitBase, _hfiber⟩
      exact ⟨hliveVar, hwitBase⟩
    · rcases htrackedNext.2.1 liveLit.var τ hnextBase with
        ⟨hliveVar, hwitBase, _hfiber⟩
      exact ⟨hliveVar, hwitBase⟩
  exact
    ⟨cref, c, changed, flipLit, liveLit, τ, σSide, hget,
      hnextFalse, hcurrentTrue, hchangedMem, hchangedVar,
      hchangedTrue, hchangedNextFalse, hchangedNextFlipFalse,
      hchangedNoPath, hnoCompl, hflipMem, hflipVar,
      hflipNextFalse, hflipNextTrue, hwitNext, hnotCand,
      hexiFlip, hcontainsFlip, hside, hbaseSide, hnotSide,
      hchangedCurrent, hnoPathCurrent, holdFalse, hfiber,
      hflipCandTrue, hflipCandFlipTrue, hliveMem, hliveBaseInfo.1,
      hliveBaseInfo.2, hliveCandTrue, hliveNextFalse⟩

/-!
The live literal found in the current-true branch has the same two shapes as
the later forward-live branch.  If it is a different variable from the changed
literal, the same-clause tail argument supplies the missing pure-path fact for
the old polarity of the live literal.  If it is the same variable, the
no-complement condition identifies it with the changed literal itself; this is
kept as a separate obstruction because it is the delicate path orientation.
-/

abbrev DependencyRemovalProperGrowthCurrentTrueLiveSameLiteralObstruction
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit liveLit τ σSide,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
    s.formula.varValue σSide skCand flipLit.var ≠
      s.formula.varValue σSide skBase flipLit.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) = false ∧
    (∀ ρ,
      deleteDepArgs s.formula flipLit.var on_ ρ =
        deleteDepArgs s.formula flipLit.var on_ σSide →
      s.formula.varValue ρ skCand flipLit.var ≠
        s.formula.varValue ρ skBase flipLit.var →
      fullDepArgs s.formula flipLit.var ρ =
        fullDepArgs s.formula flipLit.var σSide) ∧
    s.formula.litValue τ skCand flipLit = true ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = true ∧
    liveLit ∈ c.lits.toList ∧
    liveLit.var ∈ vars.toList ∧
    DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
    s.formula.litValue τ skCand liveLit = true ∧
    s.formula.litValue τ skNext liveLit = false ∧
    liveLit.var = changed.var ∧
    s.formula.litValue τ skCand changed = true

abbrev DependencyRemovalProperGrowthCurrentTrueLiveTailResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit liveLit τ σSide,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.isVarExistential flipLit.var = true ∧
    (s.formula.depset.getD flipLit.var #[]).contains on_ = true ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula flipLit.var on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand σSide ∧
    s.formula.varValue σSide skCand flipLit.var ≠
      s.formula.varValue σSide skBase flipLit.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit flipLit.var
        (s.formula.varValue σSide skBase flipLit.var)) = false ∧
    (∀ ρ,
      deleteDepArgs s.formula flipLit.var on_ ρ =
        deleteDepArgs s.formula flipLit.var on_ σSide →
      s.formula.varValue ρ skCand flipLit.var ≠
        s.formula.varValue ρ skBase flipLit.var →
      fullDepArgs s.formula flipLit.var ρ =
        fullDepArgs s.formula flipLit.var σSide) ∧
    s.formula.litValue τ skCand flipLit = true ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = true ∧
    liveLit ∈ c.lits.toList ∧
    liveLit.var ∈ vars.toList ∧
    DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
    s.formula.litValue τ skCand liveLit = true ∧
    s.formula.litValue τ skNext liveLit = false ∧
    liveLit.var ≠ changed.var ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit liveLit.var (!liveLit.isPos))

theorem dependencyRemoval_properGrowthCurrentTrueLive_tailNoPath_or_sameLiteral
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hres :
      DependencyRemovalProperGrowthCurrentTrueLiveResidual
        s vars on_ skBase skCand skNext) :
    DependencyRemovalProperGrowthCurrentTrueLiveTailResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentTrueLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨cref, c, changed, flipLit, liveLit, τ, σSide, hget,
      hnextFalse, hcurrentTrue, hchangedMem, hchangedVar,
      hchangedTrue, hchangedNextFalse, hchangedNextFlipFalse,
      hchangedNoPath, hnoCompl, hflipMem, hflipVar,
      hflipNextFalse, hflipNextTrue, hwitNext, hnotCand,
      hexiFlip, hcontainsFlip, hside, hbaseSide, hnotSide,
      hchangedCurrent, hnoPathCurrent, holdFalse, hfiber,
      hflipCandTrue, hflipCandFlipTrue, hliveMem, hliveVar,
      hliveBaseWitness, hliveCandTrue, hliveNextFalse⟩
  by_cases hsameVar : liveLit.var = changed.var
  · have hliveNeChangedNeg : liveLit ≠ changed.negate := by
      intro hEq
      exact (hnoCompl changed hchangedMem) (by simpa [← hEq] using hliveMem)
    have hliveEqChanged : liveLit = changed :=
      dependencyRemoval_literal_eq_of_same_var_and_not_negate
        changed liveLit hsameVar.symm hliveNeChangedNeg
    have hchangedCandTrue :
        s.formula.litValue τ skCand changed = true := by
      simpa [hliveEqChanged] using hliveCandTrue
    exact Or.inr
      ⟨cref, c, changed, flipLit, liveLit, τ, σSide, hget,
        hnextFalse, hcurrentTrue, hchangedMem, hchangedVar,
        hchangedTrue, hchangedNextFalse, hchangedNextFlipFalse,
        hchangedNoPath, hnoCompl, hflipMem, hflipVar,
        hflipNextFalse, hflipNextTrue, hwitNext, hnotCand,
        hexiFlip, hcontainsFlip, hside, hbaseSide, hnotSide,
        hchangedCurrent, hnoPathCurrent, holdFalse, hfiber,
        hflipCandTrue, hflipCandFlipTrue, hliveMem, hliveVar,
        hliveBaseWitness, hliveCandTrue, hliveNextFalse, hsameVar,
        hchangedCandTrue⟩
  · have hchangedMemMk :
        mkLit changed.var changed.isPos ∈ c.lits.toList := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
      exact hchangedMem
    have hliveMemMk :
        mkLit liveLit.var liveLit.isPos ∈ c.lits.toList := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos liveLit]
      exact hliveMem
    have hchangedNoPathMk :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit changed.var changed.isPos) := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
      exact hchangedNoPath
    have hothers :
        ∀ lit ∈ c.lits.toList,
          lit ≠ mkLit changed.var changed.isPos →
          s.formula.litValue τ skNext lit = false := by
      intro lit hlit _hne
      exact dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula τ skNext c.lits hnextFalse lit hlit
    have htailNoPath :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit liveLit.var (!liveLit.isPos)) :=
      dependencyRemoval_sameClause_tailOldLiteralNoPurePath
        (s := s) (vars := vars) (on_ := on_)
        (of_ := changed.var) (nextOf := liveLit.var)
        (sk := skNext) (σ := τ) (cref := cref) (c := c)
        (pos := changed.isPos) (nextPos := liveLit.isPos)
        hon_univ hexi hcontains hchangedVar hget hchangedMemMk
        hchangedNoPathMk hsameVar hliveMemMk hothers
    exact Or.inl
      ⟨cref, c, changed, flipLit, liveLit, τ, σSide, hget,
        hnextFalse, hcurrentTrue, hchangedMem, hchangedVar,
        hchangedTrue, hchangedNextFalse, hchangedNextFlipFalse,
        hchangedNoPath, hnoCompl, hflipMem, hflipVar,
        hflipNextFalse, hflipNextTrue, hwitNext, hnotCand,
        hexiFlip, hcontainsFlip, hside, hbaseSide, hnotSide,
        hchangedCurrent, hnoPathCurrent, holdFalse, hfiber,
        hflipCandTrue, hflipCandFlipTrue, hliveMem, hliveVar,
        hliveBaseWitness, hliveCandTrue, hliveNextFalse, hsameVar,
        htailNoPath⟩

abbrev DependencyRemovalProperGrowthCurrentFalseResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var))

theorem dependencyRemoval_properGrowthNewWitness_currentClauseSideSplit
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hobs :
      DependencyRemovalProperGrowthNewWitnessObstruction
        s vars on_ skBase skCand skNext) :
    DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseResidual
        s vars on_ skBase skCand skNext := by
  classical
  rcases hobs with
    ⟨cref, c, changed, flipLit, τ, σSide, hget,
      hclauseFalse, hchangedMem, hchangedVar, hchangedTrue,
      hchangedFalse, hchangedFlipFalse, hchangedNoPath, hnoCompl,
      hflipMem, hflipVar, hflipFalse, hflipTrue, hwitNext,
      hnotCand, hexiFlip, hcontainsFlip, hside, hbaseSide,
      hnotSide, hchangedCurrent, hnoPathCurrent, holdFalse,
      hfiber⟩
  have hnextBase :
      s.formula.varValue τ skNext flipLit.var =
          s.formula.varValue τ skBase flipLit.var ∧
        s.formula.varValue (flipUniv on_ τ) skNext flipLit.var =
          s.formula.varValue (flipUniv on_ τ) skBase flipLit.var :=
    dependencyRemoval_liveCandidateWitness_agreesWithBase
      (s := s) (vars := vars) (on_ := on_)
      (of_ := flipLit.var) (skBase := skBase)
      (skCand := skNext) (σ := τ)
      htrackedNext hflipVar hwitNext
  have hnextValuePol :
      s.formula.varValue τ skNext flipLit.var = !flipLit.isPos :=
    dependencyRemoval_litValue_false_varValue_eq_not_isPos
      s.formula τ skNext flipLit hflipFalse
  have hbaseValuePol :
      s.formula.varValue τ skBase flipLit.var = !flipLit.isPos :=
    hnextBase.1.symm.trans hnextValuePol
  have hnextFlipValuePol :
      s.formula.varValue (flipUniv on_ τ) skNext flipLit.var =
        flipLit.isPos :=
    dependencyRemoval_litValue_true_varValue_eq_isPos
      s.formula (flipUniv on_ τ) skNext flipLit hflipTrue
  have hbaseFlipValuePol :
      s.formula.varValue (flipUniv on_ τ) skBase flipLit.var =
        flipLit.isPos :=
    hnextBase.2.symm.trans hnextFlipValuePol
  have hdistinct : flipLit.var ≠ changed.var := by
    intro hsame
    have hnotNeg : flipLit ≠ changed.negate := by
      intro hEq
      exact (hnoCompl changed hchangedMem) (by simpa [hEq] using hflipMem)
    have hflipEqChanged : flipLit = changed :=
      dependencyRemoval_literal_eq_of_same_var_and_not_negate
        changed flipLit hsame.symm hnotNeg
    have htrueChanged :
        s.formula.litValue (flipUniv on_ τ) skNext changed = true := by
      simpa [hflipEqChanged] using hflipTrue
    rw [hchangedFlipFalse] at htrueChanged
    cases htrueChanged
  have hchangedMemMk :
      mkLit changed.var changed.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
    exact hchangedMem
  have hflipMemMk :
      mkLit flipLit.var flipLit.isPos ∈ c.lits.toList := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos flipLit]
    exact hflipMem
  have hchangedNoPathMk :
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit changed.var changed.isPos) := by
    rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
    exact hchangedNoPath
  have hothers :
      ∀ lit ∈ c.lits.toList,
        lit ≠ mkLit changed.var changed.isPos →
        s.formula.litValue τ skNext lit = false := by
    intro lit hlit _hne
    exact dependencyRemoval_clauseValue_false_implies_lit_false
      s.formula τ skNext c.lits hclauseFalse lit hlit
  have htailNoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit flipLit.var (!flipLit.isPos)) :=
    dependencyRemoval_sameClause_tailOldLiteralNoPurePath
      (s := s) (vars := vars) (on_ := on_)
      (of_ := changed.var) (nextOf := flipLit.var)
      (sk := skNext) (σ := τ) (cref := cref) (c := c)
      (pos := changed.isPos) (nextPos := flipLit.isPos)
      hon_univ hexi hcontains hchangedVar hget hchangedMemMk
      hchangedNoPathMk hdistinct hflipMemMk hothers
  have htailBase :
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit flipLit.var
          (s.formula.varValue τ skBase flipLit.var)) := by
    simpa [hbaseValuePol] using htailNoPath
  have hwitBaseτ :
      DeleteDepWitness s.formula flipLit.var on_ skBase τ := by
    unfold DeleteDepWitness
    rw [hbaseValuePol, hbaseFlipValuePol]
    cases flipLit.isPos <;> simp
  have hcandEq :
      s.formula.varValue τ skCand flipLit.var =
        s.formula.varValue (flipUniv on_ τ) skCand flipLit.var := by
    by_cases hEq :
        s.formula.varValue τ skCand flipLit.var =
          s.formula.varValue (flipUniv on_ τ) skCand flipLit.var
    · exact hEq
    · exact False.elim (hnotCand hEq)
  rcases
      dependencyRemoval_removedBaseWitness_sideSplit_opposite_agrees
        s.formula flipLit.var on_ skBase skCand τ σSide
        hwitBaseτ hnotCand hside hchangedCurrent with
    horient | horient
  · rcases horient with ⟨hσSide, hagreeFlip⟩
    subst σSide
    have hcandτ :
        s.formula.varValue τ skCand flipLit.var = flipLit.isPos := by
      cases hpos : flipLit.isPos <;>
        cases hcand : s.formula.varValue τ skCand flipLit.var <;>
        simp [hpos, hcand, hbaseValuePol] at hchangedCurrent ⊢
    have hcandFlip :
        s.formula.varValue (flipUniv on_ τ) skCand flipLit.var =
          flipLit.isPos := by
      rw [hagreeFlip, hbaseFlipValuePol]
    have hlitτ :
        s.formula.litValue τ skCand flipLit = true :=
      dependencyRemoval_varValue_eq_isPos_litValue_true
        s.formula τ skCand flipLit hcandτ
    have hlitFlip :
        s.formula.litValue (flipUniv on_ τ) skCand flipLit = true :=
      dependencyRemoval_varValue_eq_isPos_litValue_true
        s.formula (flipUniv on_ τ) skCand flipLit hcandFlip
    exact Or.inl
      ⟨cref, c, changed, flipLit, τ, τ, hget, hclauseFalse,
        dependencyRemoval_clauseValue_true_of_mem_lit_true
          s.formula τ skCand hflipMem hlitτ,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipVar, hflipFalse, hflipTrue, hwitNext, hnotCand,
        hexiFlip, hcontainsFlip, Or.inl rfl, hbaseSide, hnotSide,
        hchangedCurrent, hnoPathCurrent, holdFalse, hfiber, hlitτ,
        hlitFlip⟩
  · rcases horient with ⟨hσSide, hagreeτ⟩
    subst σSide
    have hcandFlip :
        s.formula.varValue (flipUniv on_ τ) skCand flipLit.var =
          !flipLit.isPos := by
      cases hpos : flipLit.isPos <;>
        cases hcand :
          s.formula.varValue (flipUniv on_ τ) skCand flipLit.var <;>
        simp [hpos, hcand, hbaseFlipValuePol] at hchangedCurrent ⊢
    have hcandτ :
        s.formula.varValue τ skCand flipLit.var = !flipLit.isPos :=
      hcandEq.trans hcandFlip
    have hlitτ :
        s.formula.litValue τ skCand flipLit = false :=
      dependencyRemoval_varValue_eq_not_isPos_litValue_false
        s.formula τ skCand flipLit hcandτ
    have hlitFlip :
        s.formula.litValue (flipUniv on_ τ) skCand flipLit = false :=
      dependencyRemoval_varValue_eq_not_isPos_litValue_false
        s.formula (flipUniv on_ τ) skCand flipLit hcandFlip
    have htailCand :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit flipLit.var
            (s.formula.varValue τ skCand flipLit.var)) := by
      simpa [hcandτ, hbaseValuePol] using htailBase
    exact Or.inr
      ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipVar, hflipFalse, hflipTrue, hwitNext, hnotCand,
        hlitτ, hlitFlip, htailCand⟩

/-!
If the current-false proper-growth residual is not already a same-clause
failure, the current candidate must make the residual clause true on at least
one \(u\)-side.  The side \(\tau\) is the directly useful case: because the
two-patch candidate falsifies the same clause at \(\tau\), Lean can name a
literal that was true for the current candidate and false for the two-patch
candidate.
-/

abbrev DependencyRemovalProperGrowthCurrentFalseForwardLiveResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var)) ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    ∃ liveLit,
      liveLit ∈ c.lits.toList ∧
      s.formula.litValue τ skCand liveLit = true ∧
      s.formula.litValue τ skNext liveLit = false

/-!
In the forward-live residual, the current candidate satisfies the residual
clause at \(\tau\) through some literal `liveLit`, while the two-patch
candidate falsifies that same literal.  The tracked footprints for the current
candidate and the two-patch candidate show that this live literal belongs to
the original dependency-removal pool and is already a dependency witness of
the original Skolem functions.

If `liveLit` is not the old changed literal, the same-clause tail argument
also gives the missing pure-path condition for the old polarity of `liveLit`.
The remaining same-variable case is normalized separately: no complementary
pair in the clause forces `liveLit` to be exactly the old changed literal.
-/

abbrev DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var)) ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    s.formula.litValue τ skCand changed = true

abbrev DependencyRemovalProperGrowthForwardLiveTailResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit liveLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var)) ∧
    s.formula.clauseValue τ skCand c.lits = true ∧
    liveLit ∈ c.lits.toList ∧
    liveLit.var ∈ vars.toList ∧
    DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
    s.formula.litValue τ skCand liveLit = true ∧
    s.formula.litValue τ skNext liveLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit liveLit.var (!liveLit.isPos))

theorem dependencyRemoval_properGrowthCurrentFalseForwardLive_tailNoPath_or_sameLiteral
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hres :
      DependencyRemovalProperGrowthCurrentFalseForwardLiveResidual
        s vars on_ skBase skCand skNext) :
    (∃ cref c changed flipLit liveLit τ,
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      changed ∈ c.lits.toList ∧
      changed.var ∈ vars.toList ∧
      s.formula.litValue τ skBase changed = true ∧
      s.formula.litValue τ skNext changed = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
      (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
      flipLit ∈ c.lits.toList ∧
      flipLit.var ∈ vars.toList ∧
      s.formula.litValue τ skNext flipLit = false ∧
      s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
      DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
      ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
      s.formula.litValue τ skCand flipLit = false ∧
      s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit flipLit.var
          (s.formula.varValue τ skCand flipLit.var)) ∧
      s.formula.clauseValue τ skCand c.lits = true ∧
      liveLit ∈ c.lits.toList ∧
      liveLit.var ∈ vars.toList ∧
      DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
      s.formula.litValue τ skCand liveLit = true ∧
      s.formula.litValue τ skNext liveLit = false ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
        (mkLit liveLit.var (!liveLit.isPos))) ∨
      DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
      hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
      hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
      hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
      hnotCand, hflipCandFalse, hflipCandFlipFalse,
      hnoPathCurrent, hcurrentTrue, liveLit, hliveMem,
      hliveCandTrue, hliveNextFalse⟩
  have hdiffNextCand :
      s.formula.varValue τ skNext liveLit.var ≠
        s.formula.varValue τ skCand liveLit.var :=
    dependencyRemoval_litValue_true_false_varValue_ne
      s.formula τ skCand skNext liveLit hliveCandTrue hliveNextFalse
  have hliveBaseInfo :
      liveLit.var ∈ vars.toList ∧
        DeleteDepWitness s.formula liveLit.var on_ skBase τ := by
    by_cases hnextBase :
        s.formula.varValue τ skNext liveLit.var =
          s.formula.varValue τ skBase liveLit.var
    · have hcandBase :
          s.formula.varValue τ skCand liveLit.var ≠
            s.formula.varValue τ skBase liveLit.var := by
        intro hcandBase
        exact hdiffNextCand (hnextBase.trans hcandBase.symm)
      rcases htracked.2.1 liveLit.var τ hcandBase with
        ⟨hliveVar, hwitBase, _hfiber⟩
      exact ⟨hliveVar, hwitBase⟩
    · rcases htrackedNext.2.1 liveLit.var τ hnextBase with
        ⟨hliveVar, hwitBase, _hfiber⟩
      exact ⟨hliveVar, hwitBase⟩
  by_cases hsameVar : liveLit.var = changed.var
  · have hliveNeChangedNeg : liveLit ≠ changed.negate := by
      intro hEq
      exact (hnoCompl changed hchangedMem) (by simpa [← hEq] using hliveMem)
    have hliveEqChanged : liveLit = changed :=
      dependencyRemoval_literal_eq_of_same_var_and_not_negate
        changed liveLit hsameVar.symm hliveNeChangedNeg
    have hchangedCandTrue :
        s.formula.litValue τ skCand changed = true := by
      simpa [hliveEqChanged] using hliveCandTrue
    exact Or.inr
      ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
        hnotCand, hflipCandFalse, hflipCandFlipFalse,
        hnoPathCurrent, hcurrentTrue, hchangedCandTrue⟩
  · have hchangedMemMk :
        mkLit changed.var changed.isPos ∈ c.lits.toList := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
      exact hchangedMem
    have hliveMemMk :
        mkLit liveLit.var liveLit.isPos ∈ c.lits.toList := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos liveLit]
      exact hliveMem
    have hchangedNoPathMk :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit changed.var changed.isPos) := by
      rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
      exact hchangedNoPath
    have hothers :
        ∀ lit ∈ c.lits.toList,
          lit ≠ mkLit changed.var changed.isPos →
          s.formula.litValue τ skNext lit = false := by
      intro lit hlit _hne
      exact dependencyRemoval_clauseValue_false_implies_lit_false
        s.formula τ skNext c.lits hnextFalse lit hlit
    have htailNoPath :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit liveLit.var (!liveLit.isPos)) :=
      dependencyRemoval_sameClause_tailOldLiteralNoPurePath
        (s := s) (vars := vars) (on_ := on_)
        (of_ := changed.var) (nextOf := liveLit.var)
        (sk := skNext) (σ := τ) (cref := cref) (c := c)
        (pos := changed.isPos) (nextPos := liveLit.isPos)
        hon_univ hexi hcontains hchangedVar hget hchangedMemMk
        hchangedNoPathMk hsameVar hliveMemMk hothers
    exact Or.inl
      ⟨cref, c, changed, flipLit, liveLit, τ, hget, hnextFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
        hnotCand, hflipCandFalse, hflipCandFlipFalse,
        hnoPathCurrent, hcurrentTrue, hliveMem, hliveBaseInfo.1,
        hliveBaseInfo.2, hliveCandTrue, hliveNextFalse,
        htailNoPath⟩

theorem dependencyRemoval_properGrowthCurrentFalseForwardLive_tailResidual_or_sameLiteral
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hres :
      DependencyRemovalProperGrowthCurrentFalseForwardLiveResidual
        s vars on_ skBase skCand skNext) :
    DependencyRemovalProperGrowthForwardLiveTailResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext := by
  simpa [DependencyRemovalProperGrowthForwardLiveTailResidual] using
    dependencyRemoval_properGrowthCurrentFalseForwardLive_tailNoPath_or_sameLiteral
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext)
      hon_univ hexi hcontains htracked htrackedNext hres

/-!
The other live side is more delicate: the current candidate still falsifies
the residual clause at \(\tau\), but satisfies it after flipping \(u\).  This
is the exact "some other literal on the flipped side" situation from the TeX
argument, kept separate so the next proof can either patch it or expose the
remaining path obstruction.
-/

abbrev DependencyRemovalProperGrowthCurrentFalseFlipLiveResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var)) ∧
    s.formula.clauseValue τ skCand c.lits = false ∧
    s.formula.clauseValue (flipUniv on_ τ) skCand c.lits = true

/-!
The current-false branch must keep its residual provenance.  A bare
same-clause failure would say only that `skCand` falsifies some clause on both
universal sides; this package records that the clause is the same residual
clause produced by the two-patch analysis, with the same `changed`, `flipLit`,
and assignment data still available.
-/

abbrev DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ cref c changed flipLit τ,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    changed ∈ c.lits.toList ∧
    changed.var ∈ vars.toList ∧
    s.formula.litValue τ skBase changed = true ∧
    s.formula.litValue τ skNext changed = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext changed = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) changed ∧
    (∀ l ∈ c.lits.toList, l.negate ∉ c.lits.toList) ∧
    flipLit ∈ c.lits.toList ∧
    flipLit.var ∈ vars.toList ∧
    s.formula.litValue τ skNext flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skNext flipLit = true ∧
    DeleteDepWitness s.formula flipLit.var on_ skNext τ ∧
    ¬ DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
    s.formula.litValue τ skCand flipLit = false ∧
    s.formula.litValue (flipUniv on_ τ) skCand flipLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit flipLit.var
        (s.formula.varValue τ skCand flipLit.var)) ∧
    s.formula.clauseValue τ skCand c.lits = false ∧
    s.formula.clauseValue (flipUniv on_ τ) skCand c.lits = false

theorem dependencyRemoval_properGrowthCurrentBothSidesFalseResidual_sameClauseFailure
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext) :
    ∃ τ, FlexibleRepairSameClauseFlipFailure
      s vars on_ skBase skCand τ := by
  rcases hres with
    ⟨cref, c, _changed, _flipLit, τ, hget, _hnextFalse,
      _hchangedMem, _hchangedVar, _hchangedTrue, _hchangedFalse,
      _hchangedFlipFalse, _hchangedNoPath, _hnoCompl, _hflipMem,
      _hflipVar, _hflipNextFalse, _hflipNextTrue, _hwitNext,
      _hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent, hcurrentFalse, hcurrentFlipFalse⟩
  exact
    ⟨τ,
      dependencyRemoval_currentClauseFalse_bothSides_sameClauseFailure
        (s := s) (vars := vars) (on_ := on_)
        (skBase := skBase) (skCand := skCand) (σ := τ)
        (cref := cref) (c := c)
        hallBase htracked hget hcurrentFalse hcurrentFlipFalse⟩

theorem dependencyRemoval_properGrowthCurrentFalseResidual_refineCurrentClause
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hres :
      DependencyRemovalProperGrowthCurrentFalseResidual
        s vars on_ skBase skCand skNext) :
    DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseForwardLiveResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseFlipLiveResidual
        s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
      hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
      hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
      hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
      hnotCand, hflipCandFalse, hflipCandFlipFalse,
      hnoPathCurrent⟩
  by_cases hcurrentTrue :
      s.formula.clauseValue τ skCand c.lits = true
  · rcases clauseValue_true_false_implies_exists_true_false_lit
      s.formula τ skCand skNext c.lits hcurrentTrue hnextFalse with
      ⟨liveLit, hliveMem, hliveCandTrue, hliveNextFalse⟩
    exact Or.inr (Or.inl
      ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
        hnotCand, hflipCandFalse, hflipCandFlipFalse,
        hnoPathCurrent, hcurrentTrue, liveLit, hliveMem,
        hliveCandTrue, hliveNextFalse⟩)
  · have hcurrentFalse :
        s.formula.clauseValue τ skCand c.lits = false := by
      cases hval : s.formula.clauseValue τ skCand c.lits
      · rfl
      · exact False.elim (hcurrentTrue hval)
    by_cases hcurrentFlipFalse :
        s.formula.clauseValue (flipUniv on_ τ) skCand c.lits = false
    · exact Or.inl
        ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
          hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
          hnotCand, hflipCandFalse, hflipCandFlipFalse,
          hnoPathCurrent, hcurrentFalse, hcurrentFlipFalse⟩
    · have hcurrentFlipTrue :
          s.formula.clauseValue (flipUniv on_ τ) skCand c.lits = true := by
        cases hval :
            s.formula.clauseValue (flipUniv on_ τ) skCand c.lits
        · exact False.elim (hcurrentFlipFalse hval)
        · rfl
      exact Or.inr (Or.inr
        ⟨cref, c, changed, flipLit, τ, hget, hnextFalse,
          hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hflipVar, hflipNextFalse, hflipNextTrue, hwitNext,
          hnotCand, hflipCandFalse, hflipCandFlipFalse,
          hnoPathCurrent, hcurrentFalse, hcurrentFlipTrue⟩)

/-!
For the proper-growth residual, the TeX-style data can be exposed without
using the finite restart principle.  The ordinary strict repair branch is a
local descent step.  The ordinary pure-path obstruction is impossible by the
same-clause tail lemma.  What remains is either:

* the new-witness literal already makes the residual clause true for the
  current candidate;
* the new-witness literal is false on both \(u\)-sides for the current
  candidate, with the missing pure-path side condition for that current
  literal; or
* the same-clause failure has moved to the two-patch candidate.

This theorem is intentionally not the final induction step: it records the
noncircular frontier that still has to be closed.
-/

theorem dependencyRemoval_properGrowthResidual_sideSplit_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      (DependencyRemovalProperGrowthCurrentTrueObservedResidual
          s vars on_ skBase skCand skNext ∨
        DependencyRemovalProperGrowthCurrentFalseResidual
          s vars on_ skBase skCand skNext) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_currentStep_or_newWitnessObservation_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hclosed hgt hexi hcontains htracked htrackedNext hexact with
    hstrict | hrest
  · exact Or.inl (Or.inr hstrict)
  · rcases hrest with hpath | hrest
    · rcases hpath with
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, _hchangedTrue, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hflipFalse, hflipTrue, hwitCand, hexiFlip, hcontainsFlip,
          hpathToCurrent⟩
      have hobs :
          DependencyRemovalEquivalentFootprintPathObstruction
            s vars on_ skCand skNext :=
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, hchangedFalse,
          hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
          hflipFalse, hflipTrue, hwitCand, hexiFlip, hcontainsFlip,
          hpathToCurrent⟩
      exact False.elim
        (dependencyRemoval_equivalentFootprintPathObstruction_false
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skCand) (skNext := skNext)
          hon_univ hclosed hexi hcontains htracked htrackedNext
          hsubsetCandNext hobs)
    · rcases hrest with hnew | hsameClauseNext
      · exact Or.inr (Or.inl
          (dependencyRemoval_properGrowthNewWitness_currentClauseSideSplit
            (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
            (skCand := skCand) (skNext := skNext)
            hon_univ hexi hcontains htrackedNext hnew))
      · exact Or.inr (Or.inr hsameClauseNext)

/-!
The same result with the two side cases named.  This is the form meant for the
remaining audit: after the ordinary strict step and pure-path obstruction have
been discharged, the proof has only the current-true residual, the
current-false residual, or a same-clause failure for the two-patch candidate.
-/

theorem dependencyRemoval_properGrowthResidual_namedSideSplit_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseResidual
        s vars on_ skBase skCand skNext ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_properGrowthResidual_sideSplit_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hon_univ hclosed hgt hexi hcontains htracked htrackedNext
        hsubsetCandNext hexact with
    hlocal | hrest
  · exact Or.inl hlocal
  · rcases hrest with hside | hsame
    · rcases hside with htrue | hfalse
      · exact Or.inr (Or.inl htrue)
      · exact Or.inr (Or.inr (Or.inl hfalse))
    · exact Or.inr (Or.inr (Or.inr hsame))

/-!
Combining the previous split with the proper-growth residual theorem gives the
current audit frontier.  Apart from ordinary local repair and same-clause
failures, the remaining proper-growth cases are:

* the residual clause is already true for the current candidate at \(\tau\);
* the residual clause is true at \(\tau\) for some other current literal;
* the residual clause is false at \(\tau\), but true on the flipped side.

The last two are intentionally separate because they need different path
bookkeeping in the next proof step.
-/

theorem dependencyRemoval_properGrowthResidual_refinedSideSplit
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (_hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseForwardLiveResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentFalseFlipLiveResidual
        s vars on_ skBase skCand skNext ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_properGrowthResidual_namedSideSplit_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hon_univ hclosed hgt hexi hcontains htracked htrackedNext
        hsubsetCandNext hexact with
    hlocal | hrest
  · exact Or.inl hlocal
  · rcases hrest with htrue | hrest
    · exact Or.inr (Or.inl htrue)
    · rcases hrest with hfalse | hsameNext
      · rcases
          dependencyRemoval_properGrowthCurrentFalseResidual_refineCurrentClause
            (s := s) (vars := vars) (on_ := on_)
            (skBase := skBase) (skCand := skCand) (skNext := skNext)
            hfalse with
          hboth | hlive
        · exact Or.inr (Or.inr (Or.inl hboth))
        · rcases hlive with hforward | hflip
          · exact Or.inr (Or.inr (Or.inr (Or.inl hforward)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hflip))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsameNext))))

/-!
The same flip-live residual can be phrased closer to the TeX obstruction.  If
the live witness is on a different variable, the same-clause tail argument
gives the strict patch.  If it is the old changed literal itself, then either
the direct patch is still available, or the candidate contains an explicit
blocked-path branch: the old literal and its negation are both visible from the
same start side in the way the later path chase must analyze.
-/

theorem dependencyRemoval_properGrowthCurrentFalseFlipLive_strictStep_or_blockedPathBranch
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentFalseFlipLiveResidual
        s vars on_ skBase skCand skNext) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      ∃ startPos,
        PatchPoolBlockedPathBranch s vars on_ startPos skBase skCand := by
  classical
  rcases hres with
    ⟨cref, c, changed, flipLit, τ, hget, _hnextFalse,
      hchangedMem, hchangedVar, hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, hchangedNoPath, hnoCompl, _hflipMem,
      _hflipVar, _hflipNextFalse, _hflipNextTrue, _hwitNext,
      _hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent, hcurrentFalse, hcurrentFlipTrue⟩
  rcases dependencyRemoval_flipWitness_isExistential_or_sameClauseFalse
      (s := s) (vars := vars) (on_ := on_) (skCand := skCand)
      (σ := τ) (cref := cref) (c := c) (baseLit := changed)
      hgt hexi hcontains hget hcurrentFalse hchangedMem hchangedVar
      hchangedNoPath with
    ⟨_hnoComplCurrent, hflipOrSame⟩
  rcases hflipOrSame with hflip | hsameFalse
  · rcases hflip with
      ⟨liveLit, hliveMem, hliveFalse, hliveTrue, hliveWitness,
        hliveExi, hliveContains⟩
    by_cases hsameVar : liveLit.var = changed.var
    · have hliveNeChangedNeg : liveLit ≠ changed.negate := by
        intro hEq
        exact (hnoCompl changed hchangedMem) (by simpa [← hEq] using hliveMem)
      have hliveEqChanged : liveLit = changed :=
        dependencyRemoval_literal_eq_of_same_var_and_not_negate
          changed liveLit hsameVar.symm hliveNeChangedNeg
      have hchangedCandFalse :
          s.formula.litValue τ skCand changed = false := by
        simpa [hliveEqChanged] using hliveFalse
      have hchangedCandFlipTrue :
          s.formula.litValue (flipUniv on_ τ) skCand changed = true := by
        simpa [hliveEqChanged] using hliveTrue
      have hchangedWitness :
          DeleteDepWitness s.formula changed.var on_ skCand τ := by
        simpa [hliveEqChanged] using hliveWitness
      have hchangedExi :
          s.formula.isVarExistential changed.var = true :=
        hexi changed.var hchangedVar
      have hchangedContains :
          (s.formula.depset.getD changed.var #[]).contains on_ = true :=
        hcontains changed.var hchangedVar
      by_cases hnoPatchPath :
          ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
            (mkLit changed.var
              (s.formula.varValue τ skCand changed.var))
      · exact Or.inl
          (dependencyRemoval_poolPatchStep_trackedStrictStep
            (s := s) (vars := vars) (on_ := on_)
            (patched := changed.var) (skBase := skBase)
            (skCand := skCand) (σSeed := τ)
            hexi hcontains htracked hchangedVar hchangedWitness
            hnoPatchPath)
      · have hpathPatch :
            DeletePurePath s on_ (mkLit on_ (!(τ on_)))
              (mkLit changed.var
                (s.formula.varValue τ skCand changed.var)) :=
          Classical.byContradiction hnoPatchPath
        have hchangedNegEq :
            changed.negate =
              mkLit changed.var
                (s.formula.varValue τ skCand changed.var) :=
          dependencyRemoval_litValue_false_negate_eq_mkLit_varValue
            s.formula τ skCand changed hchangedCandFalse
        have hpathNeg :
            DeletePurePath s on_ (mkLit on_ (!(τ on_)))
              changed.negate := by
          simpa [hchangedNegEq] using hpathPatch
        exact Or.inr
          ⟨τ on_, τ, cref, c, changed, hget, hcurrentFalse,
            hnoCompl, hchangedMem, hchangedVar, rfl, hchangedTrue,
            hchangedCandFalse, hchangedNoPath, hchangedWitness,
            hchangedExi, hchangedContains, hpathNeg⟩
    · have hliveVar : liveLit.var ∈ vars.toList :=
        hclosed liveLit.var hliveExi hliveContains
      have hchangedMemMk :
          mkLit changed.var changed.isPos ∈ c.lits.toList := by
        rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
        exact hchangedMem
      have hliveMemMk :
          mkLit liveLit.var liveLit.isPos ∈ c.lits.toList := by
        rw [← dependencyRemoval_literal_eq_mkLit_var_isPos liveLit]
        exact hliveMem
      have hchangedNoPathMk :
          ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
            (mkLit changed.var changed.isPos) := by
        rw [← dependencyRemoval_literal_eq_mkLit_var_isPos changed]
        exact hchangedNoPath
      have hothers :
          ∀ l ∈ c.lits.toList, l ≠ mkLit changed.var changed.isPos →
            s.formula.litValue τ skCand l = false := by
        intro l hl _hne
        exact dependencyRemoval_clauseValue_false_implies_lit_false
          s.formula τ skCand c.lits hcurrentFalse l hl
      have htailNoPath :
          ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
            (mkLit liveLit.var (!liveLit.isPos)) :=
        dependencyRemoval_sameClause_tailOldLiteralNoPurePath
          (s := s) (vars := vars) (on_ := on_)
          (of_ := changed.var) (nextOf := liveLit.var)
          (sk := skCand) (σ := τ) (cref := cref) (c := c)
          (pos := changed.isPos) (nextPos := liveLit.isPos)
          hon_univ hexi hcontains hchangedVar hget hchangedMemMk
          hchangedNoPathMk hsameVar hliveMemMk hothers
      have hliveValue :
          s.formula.varValue τ skCand liveLit.var = !liveLit.isPos :=
        dependencyRemoval_litValue_false_varValue_eq_not_isPos
          s.formula τ skCand liveLit hliveFalse
      have hnoPathCurrent :
          ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
            (mkLit liveLit.var
              (s.formula.varValue τ skCand liveLit.var)) := by
        simpa [hliveValue] using htailNoPath
      exact Or.inl
        (dependencyRemoval_poolPatchStep_trackedStrictStep
          (s := s) (vars := vars) (on_ := on_) (patched := liveLit.var)
          (skBase := skBase) (skCand := skCand) (σSeed := τ)
          hexi hcontains htracked hliveVar hliveWitness hnoPathCurrent)
  · rw [hcurrentFlipTrue] at hsameFalse
    cases hsameFalse

/-!
The flip-live side can be sharpened further.  Instead of leaving the
same-literal case as an unnamed obstruction, Lean now records the concrete
blocked-path branch: either the candidate can be patched strictly, or the old
literal and its opposite current value form the exact blocked path data that
the later path chase must consume.
-/

theorem dependencyRemoval_properGrowthResidual_refinedSideSplit_or_blockedPathBranch
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthForwardLiveTailResidual
        s vars on_ skBase skCand skNext ∨
      DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext ∨
      (∃ startPos,
        PatchPoolBlockedPathBranch
          s vars on_ startPos skBase skCand) ∨
      ∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ := by
  rcases
      dependencyRemoval_properGrowthResidual_refinedSideSplit
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hon_univ hclosed hgt hexi hcontains hallBase htracked
        htrackedNext hsubsetCandNext hexact with
    hlocal | hrest
  · exact Or.inl hlocal
  · rcases hrest with htrue | hrest
    · exact Or.inr (Or.inl htrue)
    · rcases hrest with hboth | hrest
      · exact Or.inr (Or.inr (Or.inl hboth))
      · rcases hrest with hforward | hrest
        · rcases
            dependencyRemoval_properGrowthCurrentFalseForwardLive_tailResidual_or_sameLiteral
              (s := s) (vars := vars) (on_ := on_)
              (skBase := skBase) (skCand := skCand)
              (skNext := skNext)
              hon_univ hexi hcontains htracked htrackedNext hforward with
            htail | hsameForward
          · exact Or.inr (Or.inr (Or.inr (Or.inl htail)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsameForward))))
        · rcases hrest with hflip | hsameNext
          · rcases
              dependencyRemoval_properGrowthCurrentFalseFlipLive_strictStep_or_blockedPathBranch
                (s := s) (vars := vars) (on_ := on_)
                (skBase := skBase) (skCand := skCand)
                (skNext := skNext)
                hon_univ hclosed hgt hexi hcontains htracked hflip with
              hstrict | hblocked
            · exact Or.inl (Or.inr hstrict)
            · exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hblocked)))))
          · exact Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsameNext)))))

/-!
The hard audit point is the phrase in the TeX proof saying that the next
Skolem set \(f''\) is again in \(\mathcal M\) and has a proper subset of the
current \(u\)-dependency witnesses.  Lean does not get that conclusion from the
false residual clause in one step.

The split above names the cases hidden inside that sentence.

* `DependencyRemovalProperGrowthCurrentTrueLiveTailResidual`: the residual
  clause is false for the two-patch candidate `skNext`, but already true for
  the current candidate `skCand` through a named live clause literal.  This
  package is the non-same-variable case for the TeX proof's \(l_y\), with the
  same-clause tail no-path fact recorded.

* `DependencyRemovalProperGrowthCurrentTrueLiveSameLiteralObstruction`: the
  current-true live literal is the same variable as the changed literal.  This
  is kept separate only long enough for Lean to prove the immediate reduction:
  either it is still a current witness and gives a strict patch, or it is the
  same removed-current-witness situation as the tail case.

* `DependencyRemovalProperGrowthForwardLiveTailResidual`: a different current
  literal explains why the same clause is true for `skCand`.  If that literal
  is still a current witness, Lean now proves the TeX \(y\)-patch as a strict
  repair; otherwise it reduces to the removed-current-witness situation.

* `DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction`: the live
  literal is the same variable as the changed literal.  It has the same
  current-witness split as the previous item: strict patch if the witness is
  still present, removed-current-witness otherwise.

* `DependencyRemovalProperGrowthCurrentBothSidesFalseResidual`: the residual
  clause is false for the current candidate on both \(u\)-sides.  This is not
  collapsed to a bare same-clause failure, because the residual clause,
  changed literal, new-witness literal, and assignment are the provenance the
  next chase step must keep.

* `FlexibleRepairSameClauseFlipFailure ... skNext`: the same-clause failure has
  moved to the two-patch candidate.  This is a failed tracked candidate below
  `skBase`, but the current-frontier handler still needs either a strict step
  from `skCand` or a stronger rank decrease.

The blocked-path branch is no longer an open hard case: the no-cross-path
hypothesis turns it into a strict tracked patch by
`dependencyRemoval_blockedPathBranch_trackedStrictStep`.

After the reductions below, the reviewer-facing question is narrower: the only
frontier obligations left are the removed-current-witness state, the
current-both-sides-false residual, and a same-clause failure for the two-patch
candidate.
-/

/-!
The same case split can also feed the ranked finite-descent wrapper.  This is
the honest shape for residual cases where the next two-patch candidate is not an
immediate repair from \(f'\): the case may still make progress by lowering a
stronger rank.
-/

abbrev DependencyRemovalSameClauseConcreteCurrentFrontierRankProgress
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

/-!
For the final residual, the proof should not forget which nondecreasing
footprint branch produced the current frontier.  Proper growth says that the
two-patch candidate has gained a witness fiber relative to the current
candidate.  Equivalent footprint says the current and two-patch candidates
have the same witness fibers.  Both contain the current frontier, but the
distinction matters for any state-ranked continuation.
-/

inductive DependencyRemovalNondecreasingFrontierContext
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment)
    (σ : UnivAssignment) : Prop where
  | properGrowth :
      DependencyRemovalProperGrowthFrontier
        s vars on_ skBase skCand skNext σ →
      DependencyRemovalNondecreasingFrontierContext
        s vars on_ skBase skCand skNext σ
  | equivalentFootprint :
      DependencyRemovalEquivalentFootprintFrontier
        s vars on_ skBase skCand skNext σ →
      DependencyRemovalNondecreasingFrontierContext
        s vars on_ skBase skCand skNext σ

theorem dependencyRemoval_nondecreasingFrontierContext_of_exactResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext : FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsplitCandNext :
      deleteWitnessFiberCountSet s.formula vars on_ skCand <
          deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
        DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hnot_lt :
      ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skCand)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalNondecreasingFrontierContext
      s vars on_ skBase skCand skNext σ := by
  rcases dependencyRemoval_sameClauseConcreteNondecreasingResidual_split
      (s := s) (vars := vars) (on_ := on_)
      (skCand := skCand) (skNext := skNext)
      hsubsetCandNext hsplitCandNext hnot_lt with
    hproperCandNext | hequivFootprint
  · exact DependencyRemovalNondecreasingFrontierContext.properGrowth
      (dependencyRemoval_exactTwoPatchResidual_properGrowthFrontier_data
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi htracked htrackedNext hproperCandNext hexact)
  · rcases hequivFootprint with ⟨hsubsetNextCand, _hcountEq⟩
    exact DependencyRemovalNondecreasingFrontierContext.equivalentFootprint
      (dependencyRemoval_exactTwoPatchResidual_equivalentFrontier_data
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi hsubsetCandNext hsubsetNextCand hexact)

abbrev DependencyRemovalSameClauseConcreteNondecreasingContextRankProgress
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    (deleteWitnessFiberCountSet s.formula vars on_ skCand <
        deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand) →
    ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalNondecreasingFrontierContext
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidualRankProgress_of_contextProgress
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontext :
      DependencyRemovalSameClauseConcreteNondecreasingContextRankProgress
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsplitCandNext hnot_lt hexact
  exact hcontext hall htracked hfalse hfailure hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsplitCandNext hnot_lt hexact
    (dependencyRemoval_nondecreasingFrontierContext_of_exactResidual
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked htrackedNext hsubsetCandNext hsplitCandNext
      hnot_lt hexact)

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidualRankProgress_of_currentFrontierProgress
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierRankProgress
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsplitCandNext hnot_lt hexact
  rcases dependencyRemoval_sameClauseConcreteNondecreasingResidual_split
      (s := s) (vars := vars) (on_ := on_)
      (skCand := skCand) (skNext := skNext)
      hsubsetCandNext hsplitCandNext hnot_lt with
    hproperCandNext | hequivFootprint
  · exact hcurrent hall htracked hfalse hfailure hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      (dependencyRemoval_exactTwoPatchResidual_properGrowthFrontier_data
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi htracked htrackedNext hproperCandNext hexact).2.2.2
      hexact
  · rcases hequivFootprint with ⟨hsubsetNextCand, _hcountEq⟩
    exact hcurrent hall htracked hfalse hfailure hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      (dependencyRemoval_equivalentFrontier_currentResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        (dependencyRemoval_exactTwoPatchResidual_equivalentFrontier_data
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skCand) (skNext := skNext) (σ := σ)
          hexi hsubsetCandNext hsubsetNextCand hexact))
      hexact

/-!
The local case analysis now has the shape needed by the finite restart
principle: every failed tracked repair candidate either already gives the
descent outcome, or it gives a strictly smaller tracked repair candidate.
-/

theorem dependencyRemoval_trackedStrictFalseStep_of_sameClauseResidualHandler
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_) :
    DependencyRemovalTrackedStrictFalseStep s vars on_ := by
  classical
  intro skBase skCand σ hallBase htracked hproper hfalse
  rcases
      dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_sameClauseFailure
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
        (on_ := on_) (skBase := skBase) (skCand := skCand) (σ := σ)
        hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
        htracked hallBase hfalse with
    hstrict | hfailure
  · exact Or.inr hstrict
  · exact
      dependencyRemoval_sameClauseFailure_currentStrictStep_or_outcome_of_residualHandler
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hexi hcontains hhandler hallBase htracked hproper hfalse
        hfailure

theorem dependencyRemoval_trackedFalseRestart_of_sameClauseResidualHandler
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_trackedStrictFalseStep
    (s := s) (vars := vars) (on_ := on_)
    (dependencyRemoval_trackedStrictFalseStep_of_sameClauseResidualHandler
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths hhandler)

/-!
Equivalently, it is enough to handle the shared current-frontier form of the
same-clause residual.  The finite descent wrapper then supplies the restart
principle used by the high-level dependency-removal bridge.
-/

theorem dependencyRemoval_trackedFalseRestart_of_sameClauseCurrentFrontierHandler
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierHandler
        s vars on_) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_sameClauseResidualHandler
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_current
      (s := s) (vars := vars) (on_ := on_) hexi hcurrent)

/-!
         Since the set of dependency witnesses is finite the induction step
eventually terminates with model where $(\alpha, x, u)$ is no longer a
dependency witness, and we have strictly fewer dependency witnesses on
$u$.
         We can repeat this for any other witness $(\alpha', x, u)$ until all
witnesses of $(\alpha', x, u)$ are removed to get model $f^*$. We can
restrict the domain of $f^*_x$ to remove $u$ and it will still be well
defined and a winning Skolem function.
-/

theorem dependencyRemovalBridge_of_finite_descent
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hdescent :
      ∀ {of_ : Var} {sk : SkolemAssignment} {σ₀ : UnivAssignment},
        (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
        of_ ∈ vars.toList →
        DeleteDepWitness s.formula of_ on_ sk σ₀ →
        ∃ sk',
          (∀ σ, s.clauses.matrixValue s.formula σ sk' = true) ∧
          deleteWitnessFiberCountSet s.formula vars on_ sk' <
            deleteWitnessFiberCountSet s.formula vars on_ sk) :
    DeleteIndependenceSetBridge s vars on_ := by
  classical
  intro htrue
  rcases htrue with ⟨sk, hall⟩
  let P : Nat → Prop := fun n =>
    ∀ sk,
      deleteWitnessFiberCountSet s.formula vars on_ sk = n →
      (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
      ∃ sk',
        (∀ σ, s.clauses.matrixValue s.formula σ sk' = true) ∧
        ExhibitsDeleteIndependenceSet s.formula vars on_ sk'
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih sk hcount hall
      by_cases hcount0 :
          deleteWitnessFiberCountSet s.formula vars on_ sk = 0
      · have hexhibit :
            ExhibitsDeleteIndependenceSet s.formula vars on_ sk := by
          exact (deleteWitnessFiberCountSet_zero_iff_exhibits
            s.formula vars on_ sk hexi).1 hcount0
        exact ⟨sk, hall, hexhibit⟩
      · have hwitExists :
            ∃ of_, of_ ∈ vars.toList ∧ ∃ σ,
              DeleteDepWitness s.formula of_ on_ sk σ := by
          exact (deleteWitnessFiberCountSet_ne_zero_iff_existsDeleteDepWitness
            s.formula vars on_ sk).1 hcount0
        rcases hwitExists with ⟨of_, hof, σ₀, hwit⟩
        rcases hdescent (of_ := of_) (sk := sk) (σ₀ := σ₀) hall hof hwit with
          ⟨sk', hall', hcount_lt⟩
        have hlt_n :
            deleteWitnessFiberCountSet s.formula vars on_ sk' < n := by
          simpa [hcount] using hcount_lt
        exact ih (deleteWitnessFiberCountSet s.formula vars on_ sk') hlt_n
          sk' rfl hall')
  exact hP (deleteWitnessFiberCountSet s.formula vars on_ sk) sk rfl hall

/-!
The TeX proof chooses the side of the witness so that the first patch is on the
allowed side: if the path obstruction appears for \(\alpha\), swap to
\(\alpha^u\).  Lean records that choice as an explicit seed-selection lemma.
-/

theorem dependencyRemoval_selectSeed_of_noForbiddenPair
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {sk : SkolemAssignment} {σ₀ : UnivAssignment}
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ sk σ₀) :
    ∃ σSeed,
      DeleteDepWitness s.formula of_ on_ sk σSeed ∧
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit of_ (s.formula.varValue σSeed sk of_)) := by
  classical
  let pos := s.formula.varValue σ₀ sk of_
  by_cases hleft :
      DeletePurePath s on_ (mkLit on_ (!(σ₀ on_))) (mkLit of_ pos)
  · refine ⟨flipUniv on_ σ₀, ?_, ?_⟩
    · have hflip_involutive : flipUniv on_ (flipUniv on_ σ₀) = σ₀ := by
        funext v
        by_cases hv : v = on_
        · subst v
          simp [flipUniv]
        · simp [flipUniv, hv]
      unfold DeleteDepWitness at hwit ⊢
      rw [hflip_involutive]
      exact hwit.symm
    · intro hrightSeed
      have htarget :
          s.formula.varValue (flipUniv on_ σ₀) sk of_ = !pos := by
        unfold DeleteDepWitness at hwit
        dsimp [pos]
        cases hbase : s.formula.varValue σ₀ sk of_ <;>
          cases hflip : s.formula.varValue (flipUniv on_ σ₀) sk of_ <;>
            simp [hbase, hflip] at hwit ⊢
      have hright :
          DeletePurePath s on_ (mkLit on_ (σ₀ on_)) (mkLit of_ (!pos)) := by
        simpa [flipUniv, htarget] using hrightSeed
      cases hσ : σ₀ on_
      · have hposPath :
            DeletePurePath s on_ (mkLit on_ true) (mkLit of_ pos) := by
          simpa [hσ] using hleft
        have hnegPath :
            DeletePurePath s on_ (mkLit on_ false) (mkLit of_ (!pos)) := by
          simpa [hσ] using hright
        exact hnoPair hof hposPath hnegPath
      · have hposPath :
            DeletePurePath s on_ (mkLit on_ true) (mkLit of_ (!pos)) := by
          simpa [hσ] using hright
        have hnegPath :
            DeletePurePath s on_ (mkLit on_ false) (mkLit of_ (!(!pos))) := by
          simpa [hσ] using hleft
        exact hnoPair (badOf := of_) (pos := !pos) hof hposPath hnegPath
  · exact ⟨σ₀, hwit, hleft⟩

/-!
The same seed-selection step applies inside the residual clause chase.  If the
live literal that makes the current candidate satisfy the residual clause is
still a current \(u\)-dependency witness, then it is not a hard case: choose the
allowed side of that witness and patch it.
-/

theorem dependencyRemoval_currentWitness_trackedStrictStep_of_noForbiddenPair
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand : SkolemAssignment} {σ₀ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ skCand σ₀) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand := by
  rcases dependencyRemoval_selectSeed_of_noForbiddenPair
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (sk := skCand) (σ₀ := σ₀) hnoPair hof hwit with
    ⟨σSeed, hwitSeed, hnoPathSeed⟩
  exact dependencyRemoval_poolPatchStep_trackedStrictStep
    (s := s) (vars := vars) (on_ := on_) (patched := of_)
    (skBase := skBase) (skCand := skCand) (σSeed := σSeed)
    hexi hcontains htracked hof hwitSeed hnoPathSeed

/-!
What remains in a live-tail residual is therefore very specific.  The live
literal was a dependency witness for the original satisfying Skolem functions,
but it is not a current witness.  The repair-pool footprint then says where the
current candidate already changed the original value, and the path condition
for that old literal is carried with it.
-/

abbrev DependencyRemovalRemovedCurrentWitnessObservation
    (s : CheckState) (vars : Array Var) (on_ of_ : Var)
    (skBase skCand : SkolemAssignment) (τ : UnivAssignment) : Prop :=
  ∃ σSide,
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    of_ ∈ vars.toList ∧
    DeleteDepWitness s.formula of_ on_ skBase σSide ∧
    ¬ DeleteDepWitness s.formula of_ on_ skCand σSide ∧
    s.formula.varValue σSide skCand of_ ≠
      s.formula.varValue σSide skBase of_ ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σSide on_)))
      (mkLit of_ (s.formula.varValue σSide skBase of_)) ∧
    s.formula.litValue (flipUniv on_ σSide) skCand
      (mkLit of_ (s.formula.varValue σSide skBase of_)) = false ∧
    ∀ ρ,
      deleteDepArgs s.formula of_ on_ ρ =
        deleteDepArgs s.formula of_ on_ σSide →
      s.formula.varValue ρ skCand of_ ≠
        s.formula.varValue ρ skBase of_ →
      fullDepArgs s.formula of_ ρ =
        fullDepArgs s.formula of_ σSide

theorem dependencyRemoval_removedBaseWitness_currentObservation
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand : SkolemAssignment} {τ : UnivAssignment}
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hof : of_ ∈ vars.toList)
    (hwitBase : DeleteDepWitness s.formula of_ on_ skBase τ)
    (hnotCand : ¬ DeleteDepWitness s.formula of_ on_ skCand τ) :
    DependencyRemovalRemovedCurrentWitnessObservation
      s vars on_ of_ skBase skCand τ := by
  rcases flexibleRepairPoolTracked_removed_baseWitness_changed_footprint
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (skBase := skBase) (skCand := skCand) (σ := τ)
      htracked hof hwitBase hnotCand with
    ⟨σSide, hside, hofSide, hbaseSide, hchanged, hfiber⟩
  rcases dependencyRemoval_changedValue_baseWitnessAndNoPath
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (skBase := skBase) (skCand := skCand) (σ := σSide)
      htracked hchanged with
    ⟨_hof, _hbaseSide, hnoPath⟩
  have hnotSide :
      ¬ DeleteDepWitness s.formula of_ on_ skCand σSide := by
    rcases hside with hside | hside
    · simpa [hside] using hnotCand
    · intro hwitSide
      have hwitτ :
          DeleteDepWitness s.formula of_ on_ skCand τ :=
        (dependencyRemoval_deleteDepWitness_flipUniv_iff
          s.formula of_ on_ skCand τ).1 (by
            simpa [hside] using hwitSide)
      exact hnotCand hwitτ
  have holdFalse :
      s.formula.litValue (flipUniv on_ σSide) skCand
        (mkLit of_ (s.formula.varValue σSide skBase of_)) = false :=
    dependencyRemoval_removedChangedBaseWitness_oldLiteralFalseOnFlip
      s.formula of_ on_ skBase skCand σSide
      hbaseSide hnotSide hchanged
  exact ⟨σSide, hside, hofSide, hbaseSide, hnotSide,
    hchanged, hnoPath, holdFalse, hfiber⟩

abbrev DependencyRemovalLiveTailRemovedObservation
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop :=
  ∃ liveLit τ,
    liveLit.var ∈ vars.toList ∧
    DeleteDepWitness s.formula liveLit.var on_ skBase τ ∧
    s.formula.litValue τ skCand liveLit = true ∧
    s.formula.litValue τ skNext liveLit = false ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
      (mkLit liveLit.var (!liveLit.isPos)) ∧
    DependencyRemovalRemovedCurrentWitnessObservation
      s vars on_ liveLit.var skBase skCand τ

abbrev DependencyRemovalRemovedCurrentWitnessFrontierObservation
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand : SkolemAssignment) : Prop :=
  ∃ of_ τ,
    of_ ∈ vars.toList ∧
    DeleteDepWitness s.formula of_ on_ skBase τ ∧
    ¬ DeleteDepWitness s.formula of_ on_ skCand τ ∧
    DependencyRemovalRemovedCurrentWitnessObservation
      s vars on_ of_ skBase skCand τ

theorem dependencyRemoval_removedCurrentWitnessFrontierObservation_of_liveTailRemoved
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hobs :
      DependencyRemovalLiveTailRemovedObservation
        s vars on_ skBase skCand skNext) :
    DependencyRemovalRemovedCurrentWitnessFrontierObservation
      s vars on_ skBase skCand := by
  rcases hobs with
    ⟨liveLit, τ, hliveVar, hliveBaseWitness,
      _hliveCandTrue, _hliveNextFalse, _hliveNoPath, hremoved⟩
  have hnotCandτ :
      ¬ DeleteDepWitness s.formula liveLit.var on_ skCand τ := by
    rcases hremoved with
      ⟨σSide, hside, _hofSide, _hbaseSide, hnotSide,
        _hchanged, _hnoPath, _holdFalse, _hfiber⟩
    rcases hside with hside | hside
    · simpa [hside] using hnotSide
    · intro hwitτ
      have hwitFlip :
          DeleteDepWitness s.formula liveLit.var on_ skCand
            (flipUniv on_ τ) :=
        (dependencyRemoval_deleteDepWitness_flipUniv_iff
          s.formula liveLit.var on_ skCand τ).2 hwitτ
      exact hnotSide (by simpa [hside] using hwitFlip)
  exact
    ⟨liveLit.var, τ, hliveVar, hliveBaseWitness, hnotCandτ,
      hremoved⟩

theorem dependencyRemoval_removedCurrentWitnessFrontierObservation_of_currentFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hcurrent :
      DependencyRemovalCurrentResidualFrontier
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalRemovedCurrentWitnessFrontierObservation
      s vars on_ skBase skCand := by
  rcases dependencyRemoval_currentFrontier_flipObservation
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hcurrent with
    ⟨patched, τ, σSide, hof, hnotCandτ, hbaseτ, hside,
      hbaseSide, hchanged, hnoPath, holdFalse, hfiber⟩
  have hnotSide :
      ¬ DeleteDepWitness s.formula patched on_ skCand σSide := by
    rcases hside with hside | hside
    · simpa [hside] using hnotCandτ
    · intro hwitSide
      have hwitτ :
          DeleteDepWitness s.formula patched on_ skCand τ :=
        (dependencyRemoval_deleteDepWitness_flipUniv_iff
          s.formula patched on_ skCand τ).1 (by
            simpa [hside] using hwitSide)
      exact hnotCandτ hwitτ
  exact
    ⟨patched, τ, hof, hbaseτ, hnotCandτ,
      ⟨σSide, hside, hof, hbaseSide, hnotSide, hchanged,
        hnoPath, holdFalse, hfiber⟩⟩

/-!
In the equivalent-footprint residual, every two-patch witness fiber is still a
current-candidate witness fiber.  Therefore a witness already removed from the
current candidate is also absent from the two-patch candidate.  This is the
monotone form of the TeX bookkeeping: once a particular old dependency witness
has been removed, an equivalent-footprint continuation cannot silently restore
that same fiber.
-/

theorem dependencyRemoval_removedCurrentWitnessFrontierObservation_of_subsetNextCand
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedNext : FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hobs :
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand) :
    DependencyRemovalRemovedCurrentWitnessFrontierObservation
      s vars on_ skBase skNext := by
  rcases hobs with
    ⟨of_, τ, hof, hbaseτ, hnotCandτ, _hremovedCand⟩
  have hnotNextτ :
      ¬ DeleteDepWitness s.formula of_ on_ skNext τ :=
    deleteWitnessFiberSetSubset_not_deleteDepWitness
      (f := s.formula) (vars := vars) (on_ := on_) (of_ := of_)
      (skSmall := skNext) (skBig := skCand) (σ := τ)
      (hexi of_ hof) hsubsetNextCand hof hnotCandτ
  exact
    ⟨of_, τ, hof, hbaseτ, hnotNextτ,
      dependencyRemoval_removedBaseWitness_currentObservation
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (skBase := skBase) (skCand := skNext) (τ := τ)
        htrackedNext hof hbaseτ hnotNextτ⟩

/-!
The equivalent-footprint case is the bookkeeping situation where every witness
fiber present in the two-patch candidate is already present in the current
candidate.  Therefore any residual package that still says "this is a witness
for `skNext` but not for `skCand`" is impossible in that branch.
-/

theorem dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skCand skNext : SkolemAssignment} {τ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hof : of_ ∈ vars.toList)
    (hwitNext : DeleteDepWitness s.formula of_ on_ skNext τ)
    (hnotCand : ¬ DeleteDepWitness s.formula of_ on_ skCand τ) :
    False :=
  dependencyRemoval_subsetNextCand_forbids_newWitness
    (s := s) (vars := vars) (on_ := on_) (of_ := of_)
    (skCand := skCand) (skNext := skNext) (τ := τ)
    (hexi of_ hof) hsubsetNextCand hof hwitNext hnotCand

theorem dependencyRemoval_equivalentFootprint_forbids_currentTrueObservedResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentTrueObservedResidual
        s vars on_ skBase skCand skNext) :
    False := by
  rcases hres with
    ⟨_cref, _c, _changed, flipLit, τ, _σSide, _hget,
      _hnextFalse, _hcurrentTrue, _hchangedMem, _hchangedVar,
      _hchangedTrue, _hchangedNextFalse, _hchangedNextFlipFalse,
      _hchangedNoPath, _hnoCompl, _hflipMem, hflipVar,
      _hflipNextFalse, _hflipNextTrue, hwitNext, hnotCand,
      _hexiFlip, _hcontainsFlip, _hside, _hbaseSide, _hnotSide,
      _hchangedCurrent, _hnoPathCurrent, _holdFalse, _hfiber,
      _hflipCandTrue, _hflipCandFlipTrue⟩
  exact
    dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
      (s := s) (vars := vars) (on_ := on_) (of_ := flipLit.var)
      (skCand := skCand) (skNext := skNext) (τ := τ)
      hexi hsubsetNextCand hflipVar hwitNext hnotCand

theorem dependencyRemoval_equivalentFootprint_forbids_currentFalseResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentFalseResidual
        s vars on_ skBase skCand skNext) :
    False := by
  rcases hres with
    ⟨_cref, _c, _changed, flipLit, τ, _hget, _hnextFalse,
      _hchangedMem, _hchangedVar, _hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, _hchangedNoPath, _hnoCompl,
      _hflipMem, hflipVar, _hflipNextFalse, _hflipNextTrue,
      hwitNext, hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent⟩
  exact
    dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
      (s := s) (vars := vars) (on_ := on_) (of_ := flipLit.var)
      (skCand := skCand) (skNext := skNext) (τ := τ)
      hexi hsubsetNextCand hflipVar hwitNext hnotCand

theorem dependencyRemoval_equivalentFootprint_forbids_currentBothSidesFalseResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext) :
    False := by
  rcases hres with
    ⟨_cref, _c, _changed, flipLit, τ, _hget, _hnextFalse,
      _hchangedMem, _hchangedVar, _hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, _hchangedNoPath, _hnoCompl,
      _hflipMem, hflipVar, _hflipNextFalse, _hflipNextTrue,
      hwitNext, hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent, _hcurrentFalse, _hcurrentFlipFalse⟩
  exact
    dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
      (s := s) (vars := vars) (on_ := on_) (of_ := flipLit.var)
      (skCand := skCand) (skNext := skNext) (τ := τ)
      hexi hsubsetNextCand hflipVar hwitNext hnotCand

theorem dependencyRemoval_equivalentFootprint_forbids_forwardLiveTailResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hres :
      DependencyRemovalProperGrowthForwardLiveTailResidual
        s vars on_ skBase skCand skNext) :
    False := by
  rcases hres with
    ⟨_cref, _c, _changed, flipLit, _liveLit, τ, _hget,
      _hnextFalse, _hchangedMem, _hchangedVar, _hchangedTrue,
      _hchangedNextFalse, _hchangedNextFlipFalse, _hchangedNoPath,
      _hnoCompl, _hflipMem, hflipVar, _hflipNextFalse,
      _hflipNextTrue, hwitNext, hnotCand, _hflipCandFalse,
      _hflipCandFlipFalse, _hnoPathCurrent, _hcurrentTrue,
      _hliveMem, _hliveVar, _hliveBaseWitness, _hliveCandTrue,
      _hliveNextFalse, _hliveNoPath⟩
  exact
    dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
      (s := s) (vars := vars) (on_ := on_) (of_ := flipLit.var)
      (skCand := skCand) (skNext := skNext) (τ := τ)
      hexi hsubsetNextCand hflipVar hwitNext hnotCand

theorem dependencyRemoval_equivalentFootprint_forbids_forwardSameLiteralObstruction
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hres :
      DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext) :
    False := by
  rcases hres with
    ⟨_cref, _c, _changed, flipLit, τ, _hget, _hnextFalse,
      _hchangedMem, _hchangedVar, _hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, _hchangedNoPath, _hnoCompl,
      _hflipMem, hflipVar, _hflipNextFalse, _hflipNextTrue,
      hwitNext, hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent, _hcurrentTrue, _hchangedCandTrue⟩
  exact
    dependencyRemoval_subsetNextCand_forbids_next_not_current_witness
      (s := s) (vars := vars) (on_ := on_) (of_ := flipLit.var)
      (skCand := skCand) (skNext := skNext) (τ := τ)
      hexi hsubsetNextCand hflipVar hwitNext hnotCand

/-!
The current-true live-tail case now has a sharper statement.  Either the live
literal is still a current witness and gives the next strict patch directly, or
the only remaining data is the removed-current-witness observation above.
-/

theorem dependencyRemoval_currentTrueLiveTail_strictStep_or_removedObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentTrueLiveTailResidual
        s vars on_ skBase skCand skNext) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      DependencyRemovalLiveTailRemovedObservation
        s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨_cref, _c, _changed, _flipLit, liveLit, τ, _σSide,
      _hget, _hnextFalse, _hcurrentTrue, _hchangedMem,
      _hchangedVar, _hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, _hchangedNoPath, _hnoCompl,
      _hflipMem, _hflipVar, _hflipNextFalse, _hflipNextTrue,
      _hwitNext, _hnotCandFlip, _hexiFlip, _hcontainsFlip,
      _hside, _hbaseSide, _hnotSide, _hchangedCurrent,
      _hnoPathCurrent, _holdFalse, _hfiber, _hflipCandTrue,
      _hflipCandFlipTrue, _hliveMem, hliveVar, hliveBaseWitness,
      hliveCandTrue, hliveNextFalse, _hliveNeChanged, hliveNoPath⟩
  by_cases hliveCandWitness :
      DeleteDepWitness s.formula liveLit.var on_ skCand τ
  · exact Or.inl
      (dependencyRemoval_currentWitness_trackedStrictStep_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_)
        (of_ := liveLit.var) (skBase := skBase)
        (skCand := skCand) (σ₀ := τ)
        hexi hcontains hnoPair htracked hliveVar hliveCandWitness)
  · exact Or.inr
      ⟨liveLit, τ, hliveVar, hliveBaseWitness, hliveCandTrue,
        hliveNextFalse, hliveNoPath,
        dependencyRemoval_removedBaseWitness_currentObservation
          (s := s) (vars := vars) (on_ := on_)
          (of_ := liveLit.var) (skBase := skBase)
          (skCand := skCand) (τ := τ)
          htracked hliveVar hliveBaseWitness hliveCandWitness⟩

/-!
The two same-literal obstructions also have an immediate current-witness half.
If the named same literal is still a \(u\)-dependency witness for the current
candidate, its current value is exactly the no-path literal already recorded by
the residual clause.  If not, the branch is reduced to the generic
removed-current-witness observation.
-/

theorem dependencyRemoval_currentTrueSameLiteral_strictStep_or_removedCurrentWitness
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hres :
      DependencyRemovalProperGrowthCurrentTrueLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand := by
  rcases hres with
    ⟨_cref, c, changed, _flipLit, liveLit, τ, _σSide,
      _hget, _hnextFalse, _hcurrentTrue, hchangedMem,
      _hchangedVar, _hchangedTrue, _hchangedNextFalse,
      _hchangedNextFlipFalse, hchangedNoPath, hnoCompl,
      _hflipMem, _hflipVar, _hflipNextFalse, _hflipNextTrue,
      _hwitNext, _hnotCand, _hexiFlip, _hcontainsFlip,
      _hside, _hbaseSide, _hnotSide, _hchangedCurrent,
      _hnoPathCurrent, _holdFalse, _hfiber, _hflipCandTrue,
      _hflipCandFlipTrue, hliveMem, hliveVar, hliveBaseWitness,
      hliveCandTrue, _hliveNextFalse, hsameVar, _hchangedCandTrue⟩
  have hliveEqChanged : liveLit = changed := by
    have hliveNeChangedNeg : liveLit ≠ changed.negate := by
      intro hEq
      exact (hnoCompl changed hchangedMem) (by simpa [← hEq] using hliveMem)
    exact dependencyRemoval_literal_eq_of_same_var_and_not_negate
      changed liveLit hsameVar.symm hliveNeChangedNeg
  by_cases hliveCandWitness :
      DeleteDepWitness s.formula liveLit.var on_ skCand τ
  · have htarget :
        mkLit liveLit.var (s.formula.varValue τ skCand liveLit.var) =
          changed := by
      have hval :
          s.formula.varValue τ skCand liveLit.var = liveLit.isPos :=
        dependencyRemoval_litValue_true_varValue_eq_isPos
          s.formula τ skCand liveLit hliveCandTrue
      calc
        mkLit liveLit.var (s.formula.varValue τ skCand liveLit.var)
            = mkLit liveLit.var liveLit.isPos := by rw [hval]
        _ = liveLit := (dependencyRemoval_literal_eq_mkLit_var_isPos liveLit).symm
        _ = changed := hliveEqChanged
    have hnoPathCurrent :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit liveLit.var (s.formula.varValue τ skCand liveLit.var)) := by
      simpa [htarget] using hchangedNoPath
    exact Or.inl
      (dependencyRemoval_poolPatchStep_trackedStrictStep
        (s := s) (vars := vars) (on_ := on_) (patched := liveLit.var)
        (skBase := skBase) (skCand := skCand) (σSeed := τ)
        hexi hcontains htracked hliveVar hliveCandWitness hnoPathCurrent)
  · exact Or.inr
      ⟨liveLit.var, τ, hliveVar, hliveBaseWitness, hliveCandWitness,
        dependencyRemoval_removedBaseWitness_currentObservation
          (s := s) (vars := vars) (on_ := on_)
          (of_ := liveLit.var) (skBase := skBase)
          (skCand := skCand) (τ := τ)
          htracked hliveVar hliveBaseWitness hliveCandWitness⟩

theorem dependencyRemoval_forwardSameLiteral_strictStep_or_removedCurrentWitness
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hres :
      DependencyRemovalProperGrowthForwardLiveSameLiteralObstruction
        s vars on_ skBase skCand skNext) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand := by
  rcases hres with
    ⟨_cref, _c, changed, _flipLit, τ, _hget, _hnextFalse,
      _hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
      _hchangedFlipFalse, hchangedNoPath, _hnoCompl, _hflipMem,
      _hflipVar, _hflipNextFalse, _hflipNextTrue, _hwitNext,
      _hnotCand, _hflipCandFalse, _hflipCandFlipFalse,
      _hnoPathCurrent, _hcurrentTrue, hchangedCandTrue⟩
  have hchangedBaseWitness :
      DeleteDepWitness s.formula changed.var on_ skBase τ := by
    have hdiff :
        s.formula.varValue τ skNext changed.var ≠
          s.formula.varValue τ skBase changed.var :=
      dependencyRemoval_litValue_true_false_varValue_ne
        s.formula τ skBase skNext changed hchangedTrue hchangedFalse
    exact (htrackedNext.2.1 changed.var τ hdiff).2.1
  by_cases hchangedCandWitness :
      DeleteDepWitness s.formula changed.var on_ skCand τ
  · have htarget :
        mkLit changed.var (s.formula.varValue τ skCand changed.var) =
          changed := by
      have hval :
          s.formula.varValue τ skCand changed.var = changed.isPos :=
        dependencyRemoval_litValue_true_varValue_eq_isPos
          s.formula τ skCand changed hchangedCandTrue
      calc
        mkLit changed.var (s.formula.varValue τ skCand changed.var)
            = mkLit changed.var changed.isPos := by rw [hval]
        _ = changed := (dependencyRemoval_literal_eq_mkLit_var_isPos changed).symm
    have hnoPathCurrent :
        ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_)))
          (mkLit changed.var (s.formula.varValue τ skCand changed.var)) := by
      simpa [htarget] using hchangedNoPath
    exact Or.inl
      (dependencyRemoval_poolPatchStep_trackedStrictStep
        (s := s) (vars := vars) (on_ := on_) (patched := changed.var)
        (skBase := skBase) (skCand := skCand) (σSeed := τ)
        hexi hcontains htracked hchangedVar hchangedCandWitness hnoPathCurrent)
  · exact Or.inr
      ⟨changed.var, τ, hchangedVar, hchangedBaseWitness,
        hchangedCandWitness,
        dependencyRemoval_removedBaseWitness_currentObservation
          (s := s) (vars := vars) (on_ := on_)
          (of_ := changed.var) (skBase := skBase)
          (skCand := skCand) (τ := τ)
          htracked hchangedVar hchangedBaseWitness hchangedCandWitness⟩

/-!
The forward-live tail case has the same reduction.  A current witness is a
strict local step; the only open branch is when the live literal was already
removed from the current witness set.
-/

theorem dependencyRemoval_forwardLiveTail_strictStep_or_removedObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hres :
      DependencyRemovalProperGrowthForwardLiveTailResidual
        s vars on_ skBase skCand skNext) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      DependencyRemovalLiveTailRemovedObservation
        s vars on_ skBase skCand skNext := by
  rcases hres with
    ⟨_cref, _c, _changed, _flipLit, liveLit, τ,
      _hget, _hnextFalse, _hchangedMem, _hchangedVar,
      _hchangedTrue, _hchangedFalse, _hchangedFlipFalse,
      _hchangedNoPath, _hnoCompl, _hflipMem, _hflipVar,
      _hflipNextFalse, _hflipNextTrue, _hwitNext, _hnotCandFlip,
      _hflipCandFalse, _hflipCandFlipFalse, _hnoPathCurrent,
      _hcurrentTrue, _hliveMem, hliveVar, hliveBaseWitness,
      hliveCandTrue, hliveNextFalse, hliveNoPath⟩
  by_cases hliveCandWitness :
      DeleteDepWitness s.formula liveLit.var on_ skCand τ
  · exact Or.inl
      (dependencyRemoval_currentWitness_trackedStrictStep_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_)
        (of_ := liveLit.var) (skBase := skBase)
        (skCand := skCand) (σ₀ := τ)
        hexi hcontains hnoPair htracked hliveVar hliveCandWitness)
  · exact Or.inr
      ⟨liveLit, τ, hliveVar, hliveBaseWitness, hliveCandTrue,
        hliveNextFalse, hliveNoPath,
        dependencyRemoval_removedBaseWitness_currentObservation
          (s := s) (vars := vars) (on_ := on_)
          (of_ := liveLit.var) (skBase := skBase)
          (skCand := skCand) (τ := τ)
          htracked hliveVar hliveBaseWitness hliveCandWitness⟩

/-!
At this point the residual clause chase has a better production boundary than a
single unnamed "hard case" hypothesis.  Lean keeps the concrete frontier states
that still need more argument, and it immediately discharges the branches that
already match the TeX repair step.

The constructors mean:

* `local`: the current candidate either already satisfies the matrix or has a
  strict tracked patch.
* `removedCurrentWitness`: a literal from the residual clause was a witness for
  the original Skolem functions but is no longer a current witness.
* `currentBothSidesFalse`: the same residual clause is false for the current
  candidate on both \(u\)-sides, with the residual provenance preserved.
* `nextSameClauseFailure`: the same-clause failure has moved to the two-patch
  candidate.
-/

inductive DependencyRemovalCurrentFrontierSearchStep
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop where
  | local :
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand →
      DependencyRemovalCurrentFrontierSearchStep s vars on_ skBase skCand skNext
  | removedCurrentWitness :
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand →
      DependencyRemovalCurrentFrontierSearchStep s vars on_ skBase skCand skNext
  | currentBothSidesFalse :
      DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext →
      DependencyRemovalCurrentFrontierSearchStep s vars on_ skBase skCand skNext
  | nextSameClauseFailure :
      (∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ) →
      DependencyRemovalCurrentFrontierSearchStep s vars on_ skBase skCand skNext

theorem dependencyRemoval_currentFrontier_searchStep
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentFrontierSearchStep
      s vars on_ skBase skCand skNext := by
  have hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False := by
    intro badOf pos hof hposPath hnegPath
    exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
      (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
      (on_ := on_) (of_ := badOf) (pos := pos)
      hfull hon_le hon_univ hpaths hof hposPath hnegPath
  rcases
      dependencyRemoval_properGrowthResidual_refinedSideSplit_or_blockedPathBranch
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hon_univ hclosed hgt hexi hcontains hallBase htracked
        htrackedNext hsubsetCandNext hexact with
    hlocal | hrest
  · exact DependencyRemovalCurrentFrontierSearchStep.local hlocal
  · rcases hrest with htrue | hrest
    · have hlive :
          DependencyRemovalProperGrowthCurrentTrueLiveResidual
            s vars on_ skBase skCand skNext :=
        dependencyRemoval_properGrowthCurrentTrueObserved_liveResidual
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skCand) (skNext := skNext)
          htracked htrackedNext htrue
      rcases
          dependencyRemoval_properGrowthCurrentTrueLive_tailNoPath_or_sameLiteral
            (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
            (skCand := skCand) (skNext := skNext)
            hon_univ hexi hcontains hlive with
        htail | hsame
      · rcases
            dependencyRemoval_currentTrueLiveTail_strictStep_or_removedObservation
              (s := s) (vars := vars) (on_ := on_)
              (skBase := skBase) (skCand := skCand)
              (skNext := skNext)
              hexi hcontains hnoPair htracked htail with
          hstrict | hremoved
        · exact DependencyRemovalCurrentFrontierSearchStep.local
            (Or.inr hstrict)
        · exact DependencyRemovalCurrentFrontierSearchStep.removedCurrentWitness
            (dependencyRemoval_removedCurrentWitnessFrontierObservation_of_liveTailRemoved
              (s := s) (vars := vars) (on_ := on_)
              (skBase := skBase) (skCand := skCand)
              (skNext := skNext) hremoved)
      · rcases
            dependencyRemoval_currentTrueSameLiteral_strictStep_or_removedCurrentWitness
              (s := s) (vars := vars) (on_ := on_)
              (skBase := skBase) (skCand := skCand)
              (skNext := skNext)
              hexi hcontains htracked hsame with
          hstrict | hremoved
        · exact DependencyRemovalCurrentFrontierSearchStep.local
            (Or.inr hstrict)
        · exact DependencyRemovalCurrentFrontierSearchStep.removedCurrentWitness
            hremoved
    · rcases hrest with hboth | hrest
      · exact DependencyRemovalCurrentFrontierSearchStep.currentBothSidesFalse hboth
      · rcases hrest with htail | hrest
        · rcases
              dependencyRemoval_forwardLiveTail_strictStep_or_removedObservation
                (s := s) (vars := vars) (on_ := on_)
                (skBase := skBase) (skCand := skCand)
                (skNext := skNext)
                hexi hcontains hnoPair htracked htail with
            hstrict | hremoved
          · exact DependencyRemovalCurrentFrontierSearchStep.local
              (Or.inr hstrict)
          · exact DependencyRemovalCurrentFrontierSearchStep.removedCurrentWitness
              (dependencyRemoval_removedCurrentWitnessFrontierObservation_of_liveTailRemoved
                (s := s) (vars := vars) (on_ := on_)
                (skBase := skBase) (skCand := skCand)
                (skNext := skNext) hremoved)
        · rcases hrest with hsameForward | hrest
          · rcases
                dependencyRemoval_forwardSameLiteral_strictStep_or_removedCurrentWitness
                  (s := s) (vars := vars) (on_ := on_)
                  (skBase := skBase) (skCand := skCand)
                  (skNext := skNext)
                  hexi hcontains htracked htrackedNext hsameForward with
              hstrict | hremoved
            · exact DependencyRemovalCurrentFrontierSearchStep.local
                (Or.inr hstrict)
            · exact DependencyRemovalCurrentFrontierSearchStep.removedCurrentWitness
                hremoved
          · rcases hrest with hblocked | hsameNext
            · rcases hblocked with ⟨startPos, hblockedBranch⟩
              exact DependencyRemovalCurrentFrontierSearchStep.local
                (Or.inr
                  (dependencyRemoval_blockedPathBranch_trackedStrictStep
                    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
                    (on_ := on_) (skBase := skBase) (skCand := skCand)
                    (startPos := startPos)
                    hfull hon_le hon_univ hexi hcontains hpaths htracked
                    hblockedBranch))
            · exact
                DependencyRemovalCurrentFrontierSearchStep.nextSameClauseFailure
                  hsameNext

/-!
In the equivalent-footprint branch, the `currentBothSidesFalse` search
constructor cannot occur: that package still contains a witness for `skNext`
which is absent from `skCand`.  The removed-current-witness constructor is
also stronger here, because the equivalent-footprint subset carries the
absence from `skCand` forward to `skNext`.
-/

inductive DependencyRemovalEquivalentFootprintSearchStep
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment) : Prop where
  | local :
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand →
      DependencyRemovalEquivalentFootprintSearchStep
        s vars on_ skBase skCand skNext
  | removedNextWitness :
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skNext →
      DependencyRemovalEquivalentFootprintSearchStep
        s vars on_ skBase skCand skNext
  | nextSameClauseFailure :
      (∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ) →
      DependencyRemovalEquivalentFootprintSearchStep
        s vars on_ skBase skCand skNext

theorem dependencyRemoval_equivalentFootprint_searchStep
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalEquivalentFootprintSearchStep
      s vars on_ skBase skCand skNext := by
  rcases
      dependencyRemoval_currentFrontier_searchStep
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
        (on_ := on_) (skBase := skBase) (skCand := skCand)
        (skNext := skNext) (σ := σ)
        hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
        hallBase htracked htrackedNext hsubsetCandNext hexact with
    hlocal | hremoved | hboth | hsameNext
  · exact DependencyRemovalEquivalentFootprintSearchStep.local hlocal
  · exact DependencyRemovalEquivalentFootprintSearchStep.removedNextWitness
      (dependencyRemoval_removedCurrentWitnessFrontierObservation_of_subsetNextCand
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext)
        hexi htrackedNext hsubsetNextCand hremoved)
  · exact False.elim
      (dependencyRemoval_equivalentFootprint_forbids_currentBothSidesFalseResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext)
        hexi hsubsetNextCand hboth)
  · exact DependencyRemovalEquivalentFootprintSearchStep.nextSameClauseFailure
      hsameNext

/-!
The ranked proof can now expose the two nondecreasing frontier cases without
collapsing them back into one opaque obligation.  Proper growth keeps the
new-witness frontier.  Equivalent footprint gets the smaller search step above,
where the only non-local branches are a removed witness for `skNext` or a
same-clause failure at `skNext`.
-/

abbrev DependencyRemovalSameClauseConcreteProperGrowthFrontierRankProgress
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext →
    DependencyRemovalProperGrowthFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

abbrev DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierRankProgress
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand →
    deleteWitnessFiberCountSet s.formula vars on_ skNext =
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

abbrev DependencyRemovalEquivalentFootprintSearchStepRankProgressDischarge
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand →
    deleteWitnessFiberCountSet s.formula vars on_ skNext =
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalEquivalentFootprintSearchStep
      s vars on_ skBase skCand skNext →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

abbrev DependencyRemovalEquivalentFootprintReducedRankProgressDischarge
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand →
    deleteWitnessFiberCountSet s.formula vars on_ skNext =
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    (DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skNext →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
        rank skNext < rank skCand) ∧
    ((∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ) →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
        rank skNext < rank skCand)

theorem dependencyRemoval_equivalentFootprintSearchStepRankProgressDischarge_of_reducedDischarge
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {rank : SkolemAssignment → Nat}
    (hreduced :
      DependencyRemovalEquivalentFootprintReducedRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalEquivalentFootprintSearchStepRankProgressDischarge
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsubsetNextCand hcountEq hfrontier hexact hstep
  rcases hreduced hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hsubsetNextCand hcountEq hfrontier hexact with
    ⟨hremovedNext, hsameNext⟩
  rcases hstep with hlocal | hremoved | hsame
  · exact Or.inl hlocal
  · exact hremovedNext hremoved
  · exact hsameNext hsame

theorem dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierRankProgress_of_searchStepDischarge
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hsearch :
      DependencyRemovalEquivalentFootprintSearchStepRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsubsetNextCand hcountEq hfrontier hexact
  exact hsearch hallBase htracked hfalse htwo hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsubsetNextCand hcountEq hfrontier hexact
    (dependencyRemoval_equivalentFootprint_searchStep
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (skBase := skBase) (skCand := skCand)
      (skNext := skNext) (σ := σ)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hallBase htracked htrackedNext hsubsetCandNext hsubsetNextCand
      hexact)

theorem dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierRankProgress_of_reducedDischarge
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalEquivalentFootprintReducedRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierRankProgress
      s vars on_ rank :=
  dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierRankProgress_of_searchStepDischarge
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (dependencyRemoval_equivalentFootprintSearchStepRankProgressDischarge_of_reducedDischarge
      (s := s) (vars := vars) (on_ := on_) (rank := rank)
      hreduced)

theorem dependencyRemoval_sameClauseConcreteNondecreasingContextRankProgress_of_frontierRankProgress
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {rank : SkolemAssignment → Nat}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hproper :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierRankProgress
        s vars on_ rank)
    (hequiv :
      DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierRankProgress
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteNondecreasingContextRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsplitCandNext hnot_lt hexact _hcontext
  rcases dependencyRemoval_sameClauseConcreteNondecreasingResidual_split
      (s := s) (vars := vars) (on_ := on_)
      (skCand := skCand) (skNext := skNext)
      hsubsetCandNext hsplitCandNext hnot_lt with
    hproperCandNext | hequivFootprint
  · exact hproper hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hproperCandNext
      (dependencyRemoval_exactTwoPatchResidual_properGrowthFrontier_data
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi htracked htrackedNext hproperCandNext hexact)
      hexact
  · rcases hequivFootprint with ⟨hsubsetNextCand, hcountEq⟩
    exact hequiv hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hsubsetNextCand hcountEq
      (dependencyRemoval_exactTwoPatchResidual_equivalentFrontier_data
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi hsubsetCandNext hsubsetNextCand hexact)
      hexact

/-!
A later finite-rank argument only has to consume the named frontier state.  This
keeps the search theorem above proof-relevant while avoiding another lossy
collapse of the residual cases.
-/

abbrev DependencyRemovalCurrentFrontierSearchStepRankProgressDischarge
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalCurrentFrontierSearchStep
      s vars on_ skBase skCand skNext →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

theorem dependencyRemoval_sameClauseConcreteCurrentFrontier_rankProgress_of_searchStepDischarge
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hsearch :
      DependencyRemovalCurrentFrontierSearchStepRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteCurrentFrontierRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hcurrent hexact
  have hstep :
      DependencyRemovalCurrentFrontierSearchStep
        s vars on_ skBase skCand skNext :=
    dependencyRemoval_currentFrontier_searchStep
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (skBase := skBase) (skCand := skCand)
      (skNext := skNext) (σ := σ)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hallBase htracked htrackedNext hsubsetCandNext hexact
  exact hsearch hallBase htracked hfalse htwo hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hcurrent hexact hstep

/-!
The proof above used a simplified local descent hypothesis.  The following two
Lean statements connect the actual repair pool constructed earlier in the file
to the same final conclusion.

First, one remaining witness can be patched at its chosen seed assignment.  If
that first patch is not already a model, the restart principle keeps applying
the strict local repair step until it reaches either a model or the forbidden
pair of pure paths.
-/

theorem dependencyRemoval_witnessOutcome_of_initialPatchAndRestart
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {sk : SkolemAssignment} {σSeed : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hrestart : DependencyRemovalTrackedFalseRestart s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ sk = true)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ sk σSeed)
    (hnoPath :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
        (mkLit of_ (s.formula.varValue σSeed sk of_))) :
    DependencyRemovalDescentOutcome s vars on_ sk :=
  dependencyRemoval_trackedCandidate_apply_trackedFalseRestart
    (s := s) (vars := vars) (on_ := on_) (skBase := sk)
    (skCand := patchDeleteWitnessAt s.formula of_ σSeed sk)
    hrestart hallBase
    (dependencyRemoval_initialPatch_inRepairPool
      (s := s) (vars := vars) (on_ := on_) (of_ := of_)
      (sk := sk) (σSeed := σSeed)
      hexi hcontains hof hwit hnoPath)

/-!
Second, if every remaining witness has a seed assignment whose initial patch is
on the allowed side, then the finite descent removes all witnesses for the
deleted dependency.  This is the Lean version of repeating the repair until the
new Skolem functions no longer depend on \(u\).
-/

theorem dependencyRemovalBridge_of_initialPatchRestart
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (hselect :
      ∀ {of_ : Var} {sk : SkolemAssignment} {σ₀ : UnivAssignment},
        (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
        of_ ∈ vars.toList →
        DeleteDepWitness s.formula of_ on_ sk σ₀ →
        ∃ σSeed,
          DeleteDepWitness s.formula of_ on_ sk σSeed ∧
          ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
            (mkLit of_ (s.formula.varValue σSeed sk of_)))
    (hrestart : DependencyRemovalTrackedFalseRestart s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_finite_outcome_descent
    (s := s) (vars := vars) (on_ := on_) hexi hnoPair
    (by
      intro of_ sk σ₀ hall hof hwit
      rcases hselect hall hof hwit with ⟨σSeed, hwitSeed, hnoPath⟩
      exact dependencyRemoval_witnessOutcome_of_initialPatchAndRestart
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σSeed := σSeed)
        hexi hcontains hrestart hall hof hwitSeed hnoPath)

/-!
This version removes the abstract restart assumption: the restart comes from the
tracked local repair proof and the same-clause residual handler proved above.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (hselect :
      ∀ {of_ : Var} {sk : SkolemAssignment} {σ₀ : UnivAssignment},
        (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
        of_ ∈ vars.toList →
        DeleteDepWitness s.formula of_ on_ sk σ₀ →
        ∃ σSeed,
          DeleteDepWitness s.formula of_ on_ sk σSeed ∧
          ¬ DeletePurePath s on_ (mkLit on_ (!(σSeed on_)))
            (mkLit of_ (s.formula.varValue σSeed sk of_)))
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchRestart
    (s := s) (vars := vars) (on_ := on_)
    hexi hcontains hnoPair hselect
    (dependencyRemoval_trackedFalseRestart_of_sameClauseResidualHandler
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths hhandler)

/-!
With seed selection in place, the high-level bridge no longer needs a separate
selection hypothesis.  The only remaining local proof obligation here is the
same-clause residual handler.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noForbiddenPair
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths hnoPair
    (by
      intro of_ sk σ₀ _hall hof hwit
      exact dependencyRemoval_selectSeed_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σ₀ := σ₀) hnoPair hof hwit)
    hhandler

/-!
This is the same bridge stated with the graph condition from the TeX lemma:
no crossed pure paths for the variables being repaired.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hhandler :
      DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noForbiddenPair
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (by
      intro badOf pos hof hposPath hnegPath
      exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
        (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
        (on_ := on_) (of_ := badOf) (pos := pos)
        hfull hon_le hon_univ hpaths hof hposPath hnegPath)
    hhandler

/-!
This is the same no-cross-path bridge with the ranked residual obligation
exposed.  It keeps the TeX finite-descent paragraph intact while allowing the
remaining nondecreasing same-clause cases to be discharged by a stronger rank
than the plain witness count.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_residualRank
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresRank :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankDecrease
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchRestart
    (s := s) (vars := vars) (on_ := on_)
    hexi hcontains
    (by
      intro badOf pos hof hposPath hnegPath
      exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
        (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
        (on_ := on_) (of_ := badOf) (pos := pos)
        hfull hon_le hon_univ hpaths hof hposPath hnegPath)
    (by
      intro of_ sk σ₀ _hall hof hwit
      exact dependencyRemoval_selectSeed_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σ₀ := σ₀)
        (by
          intro badOf pos hof hposPath hnegPath
          exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
            (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
            (on_ := on_) (of_ := badOf) (pos := pos)
            hfull hon_le hon_univ hpaths hof hposPath hnegPath)
        hof hwit)
    (dependencyRemoval_trackedFalseRestart_of_sameClauseResidualRank
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count hresRank)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_residualRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hresProgress :
      DependencyRemovalSameClauseConcreteNondecreasingResidualRankProgress
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchRestart
    (s := s) (vars := vars) (on_ := on_)
    hexi hcontains
    (by
      intro badOf pos hof hposPath hnegPath
      exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
        (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
        (on_ := on_) (of_ := badOf) (pos := pos)
        hfull hon_le hon_univ hpaths hof hposPath hnegPath)
    (by
      intro of_ sk σ₀ _hall hof hwit
      exact dependencyRemoval_selectSeed_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σ₀ := σ₀)
        (by
          intro badOf pos hof hposPath hnegPath
          exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
            (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
            (on_ := on_) (of_ := badOf) (pos := pos)
            hfull hon_le hon_univ hpaths hof hposPath hnegPath)
        hof hwit)
    (dependencyRemoval_trackedFalseRestart_of_sameClauseResidualRankProgress
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count hresProgress)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_contextRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hcontext :
      DependencyRemovalSameClauseConcreteNondecreasingContextRankProgress
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_residualRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_sameClauseConcreteNondecreasingResidualRankProgress_of_contextProgress
      (s := s) (vars := vars) (on_ := on_) rank hexi hcontext)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_frontierRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hproper :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierRankProgress
        s vars on_ rank)
    (hequiv :
      DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierRankProgress
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_contextRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_sameClauseConcreteNondecreasingContextRankProgress_of_frontierRankProgress
      (s := s) (vars := vars) (on_ := on_) (rank := rank)
      hexi hproper hequiv)

/-!
The residual handler has now been split into the two concrete frontier cases:
proper growth of the current-to-two-patch witness footprint, and equivalent
footprint.  This final bridge is the same no-cross-path statement, with those
two cases exposed as the remaining local proof obligations.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_frontiers
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hgrowth :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierHandler
        s vars on_)
    (hequiv :
      DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierHandler
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_frontiers
      (s := s) (vars := vars) (on_ := on_) hexi hgrowth hequiv)

/-!
Since both residual frontier cases share the current residual clause and patch
footprint, the high-level bridge can be stated with one remaining local
obligation.  This is the closest current Lean shape to the TeX induction step:
handle the residual false clause, and the finite descent wrapper does the
rest.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_currentFrontier
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierHandler
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchRestart
    (s := s) (vars := vars) (on_ := on_)
    hexi hcontains
    (by
      intro badOf pos hof hposPath hnegPath
      exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
        (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
        (on_ := on_) (of_ := badOf) (pos := pos)
        hfull hon_le hon_univ hpaths hof hposPath hnegPath)
    (by
      intro of_ sk σ₀ _hall hof hwit
      exact dependencyRemoval_selectSeed_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σ₀ := σ₀)
        (by
          intro badOf pos hof hposPath hnegPath
          exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
            (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
            (on_ := on_) (of_ := badOf) (pos := pos)
            hfull hon_le hon_univ hpaths hof hposPath hnegPath)
        hof hwit)
    (dependencyRemoval_trackedFalseRestart_of_sameClauseCurrentFrontierHandler
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths hcurrent)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_searchStepRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hsearch :
      DependencyRemovalCurrentFrontierSearchStepRankProgressDischarge
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_residualRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_sameClauseConcreteNondecreasingResidualRankProgress_of_currentFrontierProgress
      (s := s) (vars := vars) (on_ := on_) rank hexi
      (dependencyRemoval_sameClauseConcreteCurrentFrontier_rankProgress_of_searchStepDischarge
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
        (on_ := on_) rank hfull hon_le hon_univ hclosed hgt hexi
        hcontains hpaths hsearch))

/-!
After seed selection, both live-tail cases and both same-literal cases have the
same reduced shape.  If the named literal is still a current witness, it gives a
strict patch immediately.  Otherwise the remaining obligation is the removed
current witness: a base witness is no longer present in the current candidate.
-/

abbrev DependencyRemovalCurrentFrontierReducedRankProgressDischarge
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    (DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
        rank skNext < rank skCand) ∧
    (DependencyRemovalProperGrowthCurrentBothSidesFalseResidual
        s vars on_ skBase skCand skNext →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
        rank skNext < rank skCand) ∧
    ((∃ τ, FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skNext τ) →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
        rank skNext < rank skCand)

abbrev DependencyRemovalCurrentFrontierRemovedWitnessRankProgressDischarge
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalRemovedCurrentWitnessFrontierObservation
      s vars on_ skBase skCand →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand ∨
      rank skNext < rank skCand

theorem dependencyRemoval_sameClauseConcreteProperGrowthFrontierRankProgress_of_currentFrontierReducedDischarge
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalCurrentFrontierReducedRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteProperGrowthFrontierRankProgress
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    _hproperCandNext hfrontier hexact
  rcases hreduced hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hfrontier.2.2.2 hexact with
    ⟨hremoved, hboth, hsameNext⟩
  rcases dependencyRemoval_currentFrontier_searchStep
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) (skBase := skBase) (skCand := skCand)
      (skNext := skNext) (σ := σ)
      hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hallBase htracked htrackedNext hsubsetCandNext hexact with
    hlocal | hremovedCase | hbothCase | hsameNextCase
  · exact Or.inl hlocal
  · exact hremoved hremovedCase
  · exact hboth hbothCase
  · exact hsameNext hsameNextCase

theorem dependencyRemoval_currentFrontierReducedRankProgressDischarge_of_removedWitnessDischarge
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {rank : SkolemAssignment → Nat}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hremoved :
      DependencyRemovalCurrentFrontierRemovedWitnessRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalCurrentFrontierReducedRankProgressDischarge
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hcurrent hexact
  have hobs :
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand :=
    dependencyRemoval_removedCurrentWitnessFrontierObservation_of_currentFrontier
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hcurrent
  refine ⟨?_, ?_, ?_⟩
  · intro _hremovedCase
    exact hremoved hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hcurrent hexact hobs
  · intro _hboth
    exact hremoved hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hcurrent hexact hobs
  · intro _hsameNext
    exact hremoved hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hcurrent hexact hobs

theorem dependencyRemoval_currentFrontierSearchStepRankProgressDischarge_of_reducedDischarge
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {rank : SkolemAssignment → Nat}
    (hhard :
      DependencyRemovalCurrentFrontierReducedRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalCurrentFrontierSearchStepRankProgressDischarge
      s vars on_ rank := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hcurrent hexact hstep
  rcases hhard hallBase htracked hfalse htwo hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext hcurrent
      hexact with
    ⟨hremovedCurrent, hboth, hsameNext⟩
  rcases hstep with
    hlocal | hremoved | hbothCase | hsameNextCase
  · exact Or.inl hlocal
  · exact hremovedCurrent hremoved
  · exact hboth hbothCase
  · exact hsameNext hsameNextCase

theorem dependencyRemoval_sameClauseConcreteCurrentFrontier_rankProgress_of_reducedDischarge
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hhard :
      DependencyRemovalCurrentFrontierReducedRankProgressDischarge
        s vars on_ rank) :
    DependencyRemovalSameClauseConcreteCurrentFrontierRankProgress
      s vars on_ rank :=
  dependencyRemoval_sameClauseConcreteCurrentFrontier_rankProgress_of_searchStepDischarge
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) rank hfull hon_le hon_univ hclosed hgt hexi
    hcontains hpaths
    (dependencyRemoval_currentFrontierSearchStepRankProgressDischarge_of_reducedDischarge
      (s := s) (vars := vars) (on_ := on_) (rank := rank) hhard)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_reducedRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hhard :
      DependencyRemovalCurrentFrontierReducedRankProgressDischarge
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_searchStepRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_currentFrontierSearchStepRankProgressDischarge_of_reducedDischarge
      (s := s) (vars := vars) (on_ := on_) (rank := rank) hhard)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_properCurrent_reducedEquivalentRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hproperReduced :
      DependencyRemovalCurrentFrontierReducedRankProgressDischarge
        s vars on_ rank)
    (hequivReduced :
      DependencyRemovalEquivalentFootprintReducedRankProgressDischarge
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_frontierRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_sameClauseConcreteProperGrowthFrontierRankProgress_of_currentFrontierReducedDischarge
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) rank hfull hon_le hon_univ hclosed hgt hexi
      hcontains hpaths hproperReduced)
    (dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierRankProgress_of_reducedDischarge
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
      (on_ := on_) rank hfull hon_le hon_univ hclosed hgt hexi
      hcontains hpaths hequivReduced)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_removedWitnessRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hrank_count :
      ∀ {skNext skCur : SkolemAssignment},
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skCur →
        rank skNext < rank skCur)
    (hremoved :
      DependencyRemovalCurrentFrontierRemovedWitnessRankProgressDischarge
        s vars on_ rank) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_reducedRankProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_currentFrontierReducedRankProgressDischarge_of_removedWitnessDischarge
      (s := s) (vars := vars) (on_ := on_) (rank := rank)
      hexi hremoved)

/-!
        \end{proof}
-/
