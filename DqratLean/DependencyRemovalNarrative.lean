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
The same residual footprint also proves the "flipped side agrees" observation
used immediately before the proof searches the false clause for the next
existential literal.
-/

theorem dependencyRemoval_currentResidualPatchFootprint_flipSide_agreesWithBase
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hpatch :
      DependencyRemovalCurrentResidualPatchFootprint
        s vars on_ skBase skCand skNext σ) :
    ∃ patched τ σSide,
      patched ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula patched on_ skCand τ ∧
      (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
      DeleteDepWitness s.formula patched on_ skBase σSide ∧
      s.formula.varValue σSide skCand patched ≠
        s.formula.varValue σSide skBase patched ∧
      s.formula.varValue (flipUniv on_ σSide) skCand patched =
        s.formula.varValue (flipUniv on_ σSide) skBase patched := by
  rcases hpatch with
    ⟨patched, τ, σSide, hof, hnotCand, _hbaseτ, hside,
      hbaseSide, hchanged, _hfiber⟩
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
  exact ⟨patched, τ, σSide, hof, hnotCand, hside, hbaseSide,
    hchanged,
    dependencyRemoval_removedChangedBaseWitness_flipSide_agreesWithBase
      s.formula patched on_ skBase skCand σSide
      hbaseSide hnotSide hchanged⟩

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

theorem dependencyRemoval_properGrowthFrontier_patchNoPurePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalProperGrowthFrontier
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
          fullDepArgs s.formula patched σSide :=
  dependencyRemoval_currentResidualPatchFootprint_noPurePath
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    htracked
    (dependencyRemoval_properGrowthFrontier_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hfrontier)

theorem dependencyRemoval_equivalentFrontier_patchNoPurePath
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalEquivalentFootprintFrontier
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
          fullDepArgs s.formula patched σSide :=
  dependencyRemoval_currentResidualPatchFootprint_noPurePath
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    htracked
    (dependencyRemoval_equivalentFrontier_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hfrontier)

/-!
Both residual frontier cases therefore expose the same TeX-side observation:
there is a concrete changed old literal, that old literal has no pure path
from the opposite \(u\)-side, and it is false after the \(u\)-flip.
-/

theorem dependencyRemoval_properGrowthFrontier_flipObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalProperGrowthFrontier
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
    (dependencyRemoval_properGrowthFrontier_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hfrontier)

theorem dependencyRemoval_equivalentFrontier_flipObservation
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalEquivalentFootprintFrontier
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
    (dependencyRemoval_equivalentFrontier_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hfrontier)

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

theorem dependencyRemoval_sameClauseFailure_flipMatrixFalse
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfailure :
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ) :
    s.clauses.matrixValue s.formula (flipUniv on_ σ) skCand = false := by
  rcases hfailure with
    ⟨cref, c, _baseLit, hget, _hclauseFalse, hclauseFlipFalse,
      _hnoCompl, _hbaseMem, _hbaseVar, _hbaseTrue, _hbaseFalse,
      _hbaseNoPath⟩
  exact dependencyRemoval_matrixValue_false_of_false_clause
    s.formula s.clauses (flipUniv on_ σ) skCand hget
    hclauseFlipFalse

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

theorem dependencyRemoval_exactTwoPatchResidual_equivalentFlipWitnessCurrent_or_sameClauseFailureNext
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
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
      DeleteDepWitness s.formula flipLit.var on_ skCand τ ∧
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
    have hflipVar : flipLit.var ∈ vars.toList :=
      hclosed flipLit.var hexiFlip hcontainsFlip
    have hwitCand :
        DeleteDepWitness s.formula flipLit.var on_ skCand τ :=
      Classical.byContradiction (fun hnotCand =>
        (deleteWitnessFiberSetSubset_not_deleteDepWitness
          (f := s.formula) (vars := vars) (on_ := on_)
          (of_ := flipLit.var) (skSmall := skNext)
          (skBig := skCand) (σ := τ)
          hexiFlip hsubsetNextCand hflipVar hnotCand) hwitNext)
    exact Or.inl
      ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
        hchangedMem, hchangedVar, hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem,
        hflipFalse, hflipTrue, hwitCand, hexiFlip, hcontainsFlip⟩
  · exact Or.inr hsameClause

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
      dependencyRemoval_exactTwoPatchResidual_equivalentFlipWitnessCurrent_or_sameClauseFailureNext
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hclosed hgt hexi hcontains hsubsetNextCand hexact with
    hflip | hsameClause
  · rcases hflip with
      ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
        hchangedMem, hchangedVar, _hchangedTrue, hchangedFalse,
        hchangedFlipFalse, hchangedNoPath, hnoCompl, hflipMem, hflipFalse,
        hflipTrue, hwitCand, hexiFlip, hcontainsFlip⟩
    rcases
        dependencyRemoval_existentialFlipWitness_trackedStrictStep_or_purePath
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skCand) (σ := τ) (flipLit := flipLit)
          hclosed hexi hcontains htracked hwitCand hexiFlip
          hcontainsFlip with
      hstrict | hpath
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl
        ⟨cref, c, changed, flipLit, τ, hget, hclauseFalse,
          hchangedMem, hchangedVar, hchangedFalse, hchangedFlipFalse,
          hchangedNoPath, hnoCompl, hflipMem, hflipFalse, hflipTrue,
          hwitCand, hexiFlip, hcontainsFlip, hpath⟩)
  · exact Or.inr (Or.inr
      hsameClause)

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

/-- With no-cross-paths available, the path branch collapses to a strict repair
step. After this theorem the only remaining non-step branch is the same clause
remaining false on both sides of the `on_` flip. -/
theorem dependencyRemoval_failedCandidate_strictStep_or_sameClauseFailure
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
    (hpool : FlexibleRepairPoolCandidate s vars on_ skBase skCand)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    FlexibleRepairStrictStep s vars on_ skBase skCand ∨
      FlexibleRepairSameClauseFlipFailure
        s vars on_ skBase skCand σ := by
  rcases dependencyRemoval_failedCandidate_strictStep_or_pathBranch_or_sameClauseFailure
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (σ := σ)
      hclosed hgt hexi hcontains hpool hallBase hfalse with
    hstrict | hrest
  · exact Or.inl hstrict
  · rcases hrest with hbranch | hflipFalse
    · exact Or.inl
        (dependencyRemoval_pathBranch_strictStep
          (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
          (on_ := on_) (skBase := skBase) (skCand := skCand) (σ := σ)
          hfull hon_le hon_univ hexi hcontains hpaths hpool hbranch)
    · exact Or.inr hflipFalse

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
    ⟨_cref, _c, leftLit, rightLit, _hget, _hclauseFalse,
      _hclauseFlipFalse, _hnoCompl, _hleftMem, hleftVar,
      hleftTrue, hleftFalse, hleftNoPath, _hrightMem,
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
      _hclauseFlipFalse, _hnoCompl, hleftMem, hleftVar,
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
The same argument also has a ranked form.  This is the Lean version of keeping
the TeX finite-descent argument, but allowing the residual branch to use a
finer natural-valued measure than the raw witness count.

If the two-patch candidate has fewer current witnesses, the rank decreases
because the rank extends the witness count.  If it does not have fewer current
witnesses, the residual rank obligation supplies the strict decrease.
-/

theorem dependencyRemoval_sameClauseRankedRepair_of_residualRank
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
    DependencyRemovalSameClauseRankedRepair s vars on_ rank := by
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
        (skCand := skCand) (skNext := skNext) (σ := σ) hexact
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

/-!
Once the same-clause branch has a ranked repair, the ordinary failed-candidate
case split becomes a ranked false step: immediate strict repairs decrease the
rank through the witness-count component, while same-clause failures use the
ranked repair above.
-/

theorem dependencyRemoval_rankedFalseStep_of_sameClauseRankedRepair
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
    (hsameRank :
      DependencyRemovalSameClauseRankedRepair s vars on_ rank) :
    DependencyRemovalRankedFalseStep s vars on_ rank := by
  classical
  intro skBase skCand σ hallBase htracked hproper hfalse
  rcases
      dependencyRemoval_failedTrackedCandidate_trackedStrictStep_or_sameClauseFailure
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
        (on_ := on_) (skBase := skBase) (skCand := skCand) (σ := σ)
        hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
        htracked hallBase hfalse with
    hstrict | hfailure
  · rcases hstrict with ⟨skNext, htrackedNext, hltNext⟩
    by_cases hfailNext :
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false
    · rcases hfailNext with ⟨τ, hfalseNext⟩
      have hproperNext :
          DeleteWitnessFiberSetProperSubset
            s.formula vars on_ skNext skBase :=
        dependencyRemoval_trackedFalseCandidate_hasProperSubset
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skNext) (σ := τ)
          hallBase htrackedNext hfalseNext
      exact Or.inr
        ⟨skNext, htrackedNext, hproperNext, hrank_count hltNext,
          τ, hfalseNext⟩
    · exact Or.inl
        (Or.inl ⟨skNext,
          (by
            intro τ
            cases hval :
                s.clauses.matrixValue s.formula τ skNext with
            | false => exact False.elim (hfailNext ⟨τ, hval⟩)
            | true => rfl),
          htrackedNext.1.1⟩)
  · exact hsameRank hallBase htracked hproper hfalse hfailure

theorem dependencyRemoval_trackedFalseRestart_of_sameClauseRankedRepair
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
    (hsameRank :
      DependencyRemovalSameClauseRankedRepair s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_rankedFalseStep
    (s := s) (vars := vars) (on_ := on_) rank
    (dependencyRemoval_rankedFalseStep_of_sameClauseRankedRepair
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count hsameRank)

theorem dependencyRemoval_trackedFalseRestart_of_residualRank
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
  dependencyRemoval_trackedFalseRestart_of_sameClauseRankedRepair
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    hrank_count
    (dependencyRemoval_sameClauseRankedRepair_of_residualRank
      (s := s) (vars := vars) (on_ := on_) rank
      hexi hcontains hrank_count hresRank)

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
There is also a ranked version of the high-level bridge.  It has the same
mathematical content as the previous bridge, but exposes a different remaining
obligation: instead of proving a complete nondecreasing residual handler, it is
enough to supply a rank that decreases in that residual branch.
-/

theorem dependencyRemovalBridge_of_initialPatchRankedRepair_noForbiddenPair
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
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
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
    hexi hcontains hnoPair
    (by
      intro of_ sk σ₀ _hall hof hwit
      exact dependencyRemoval_selectSeed_of_noForbiddenPair
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (sk := sk) (σ₀ := σ₀) hnoPair hof hwit)
    (dependencyRemoval_trackedFalseRestart_of_residualRank
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
      hrank_count hresRank)

theorem dependencyRemovalBridge_of_initialPatchRankedRepair_noCrossPaths
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
  dependencyRemovalBridge_of_initialPatchRankedRepair_noForbiddenPair
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    rank hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (by
      intro badOf pos hof hposPath hnegPath
      exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
        (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
        (on_ := on_) (of_ := badOf) (pos := pos)
        hfull hon_le hon_univ hpaths hof hposPath hnegPath)
    hrank_count hresRank

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
        \end{proof}
-/
