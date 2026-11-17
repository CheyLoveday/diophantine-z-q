# tyz-genus results log

Task tyz-genus (2026-11-16). Base wip/leaf-fold33b 4da8d4f3; merged origin/main (up to date),
origin/wip/h29-proof, origin/wip/h11-reduce (clean merges). Build tree reflink-copied from ~/dzq-wt/leaf-fold33b
(identical Main.lean); `lake build TYZLemma29Genus TYZThm11Integral TYZProp23Printed` OK.

TYZ source ~/tyz-src/Period7.tex: NOT on this host (ls fails). TYZ line numbers below are quoted from earlier notes.

## Step 0: findings before Lean (VERIFIED by reading the files)

* F0.1 `TYZThm21Pairs` (TYZLemma29Genus.lean:91) quantifies over integer sign choices `ℓ : ℕ → ℤ` with
  `IsLcalSign ℓ` (`(ℓ m)^2 = lcalSq m` for every squarefree m ≡ 1,3 mod 8). As h11-reduce §1 found for
  `TYZLemma29PrintedNe3`, such a leaf is vacuous unless TYZ Thm 1.1 (= h11) holds, so h11 cannot be derived from
  `TYZThm21Pairs` (item (3) of the task is impossible in that form).
* F0.2 `TYZThm21Pairs` requires `1 < n`; the values L(1)^2 needs an instance with d1 d2 = 1, i.e. n = 1, which
  the leaf excludes; at n = 3, pair (3,1) only gives 𝓛(3)^2 𝓛(1)^2 = (Q(3)/3)^2 (product, not each factor).

## Step 1: TYZ Lemma 2.8 proved in Lean (no new leaf) — VERIFIED (compiled, standard axioms)

Files (helpers under ZInQKernel/Contrib/OneProof/TYZGenusFold/, development copies in scratch/tyz-genus/):
* Jacobi.lean: `jacobiSym_neg_absNorm` ((−n / N I) = 1 for N I prime to 2n, prime-ideal induction with
  `RouteK.Redei.prime_trichotomy`), `gchar_univ_mk0` (Π_{q|n} χ_q([I]) = χ₄(N I) for n ≡ 1 mod 4, Jacobi reciprocity).
* Local.lean: `dc_norm` (reduced norms on B^× twoRep(t) H), `chi0_eq_of_mem_DC`, `F_zero` (hp23's explicit
  generator F vanishes where χ₀ = −1: twist by chi0Rep + rank one + F odd at the class of 1).
* Ideles.lean: idele `aK = E·α + (1 − E)` (E = image of the idempotent of 𝔸ᶠ_ℚ at the primes of m), `τ̂(aK)`
  componentwise, `toClassGroup_aKU` (class [I] when (α) = I M, M + (N I) = O; by counts, Tau Ceti
  `finprod_unitOfPrime_zpow_count`, `count_toPrincipalIdeal_eq_neg_log_valuation`).
* Class.lean: `exists_mk0_coprime_nat`, `exists_alpha`, `normSq_tau`, `tv_zero_of_gchar` (f_n(τ̂ t) = 0 when
  Π_q χ_q(t) = −1, n ≡ 1 mod 8), `tyzLemma28Sym : TYZLemma28Sym`,
  `tyzLemma29PrintedNe3_of_thm21Pairs : TYZThm21Pairs → TYZLemma29PrintedNe3`.
* `#print axioms` for both: [propext, Classical.choice, Quot.sound].

Proof idea (differs from h29-proof §4's twist sketch only in organisation): for a class t pick I ∈ t integral
with N I prime to 2n and α ∈ I with (α) = I M, M + (N I) = O; the idele aK (N I) α lies in t. If
τ̂(aK) ∈ B^× twoRep(t') H, reduced norms give: v_r(g · N I) even at odd r (g = nrd γ), and g·nrd(twoRep t') ∈
2^ℤ(1+4ℤ₂) at 2; so N I · nrd(twoRep t') ≢ 3 (mod 4). With χ_U(t) = χ₄(N I): χ_U(t) = −1 ⇒ t'.2.2 ≠ 0 ⇒ F(t') = 0
⇒ f_n(τ̂ t) = 0. Hence χ_{T^c} f_n = χ_T f_n termwise.

## Step 2: contribution file, #discharges, manual fold — VERIFIED (compiled)

* Helpers moved to ZInQKernel/Contrib/OneProof/TYZGenusFold/{Jacobi,Local,Ideles,Class}.lean (scratch copies
  removed); final file ZInQKernel/Contrib/OneProof/TYZLemma28Sym.lean (imports TYZLemma29Genus, which defines
  TYZThm21Pairs / TYZLemma28Sym, and TYZGenusFold.Class); `lake build ZInQKernel.Contrib.OneProof.TYZLemma28Sym` OK.
* scratch/tyz-genus/Discharges.lean → Discharges-output.txt:
  `DISCHARGES [hL29] by ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs`
  `still assumes: [ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs]`, axioms [propext, Classical.choice, Quot.sound]
  (39 open hypotheses, 9305 theorems checked).
* scratch/tyz-genus/FoldCheck.lean → FoldCheck-output.txt: `frozenTarget_thm21` (frozenTarget with hL29 replaced by
  h21 : TYZThm21Pairs) and `frozenTarget_thm21'` (as an instance of the current frozenTarget): standard axioms.
  Count: TYZ hypotheses h11, hL29 → h11, h21 (2 → 2, neutral).
