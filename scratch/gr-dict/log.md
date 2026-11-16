# gr-dict results log

Base: origin/main 2880fef1 (leaf-fold31, TailZ42, sixContactMin_of_open35). Marks: VERIFIED / STANDARD / SPECULATIVE / UNVERIFIED.

## Step 0 (2026-11-16 05:20 PST)
- Merged origin/wip/gr56-prove (90b817cb) into wip/gr-dict: clean merge (new files only).
- Build tree copied from ~/dzq-check2 (same base 2880fef1).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GR56Lattice`:
  success, GR56Lattice 118 s on the leaf-fold31 base (VERIFIED). frozenTarget axioms standard (VERIFIED).

## Step 1: bypass fold removing gonzalezRotgerProp56X6 (05:40)
- Consumers in the base (grep `\.gonzalezRotgerProp56X6`, VERIFIED): only TailZ27 L105
  (`gonzalezRotgerCountX6Ab := gonzalezRotgerCountX6Ab_of_printed n.gonzalezRotgerProp56X6 n.gonzalezRotgerX6Ab`),
  then TailZ23 L783 (`gonzalezRotgerCountX6`), TailZ9 L88 (`r5count := r5fpCount_of_points`), TailK L294
  (`FS5NoCM.fibreComTrivialFull_of_leaves'' … r.r5count`, whose only R5fpCount reader is `nocm_on_witness`).
  Agrees with gr56-prove's reach.txt over frozenTarget (97682 constants).
- `scratch/gr-dict/gen_bypass.py` (adapted from st-qbar) writes `BypassFold.lean`: research generations on the live
  path copied with suffix S (ResearchLeaves3, OpenResearchLeaves 2,5,7,8,9,14..26: 19 structures), count field
  replaced by `r5le : GR56.R5fpCountLe`; 69 theorems copied with suffix _S (incl. SGRFold.research14_of_open29,
  heckeSqrtBranchAny_of_open29, G0RevIsog.reverseIsogeny_of_leaves3); 18 forwarding lines replaced;
  TailK consumer → `FS5NoCM.fibreComTrivialFull_of_leaves''_le … r.r5le` (gr56-prove).
  New top: `OpenResearchLeaves26E` (field `eichlerOptEmbCount6 : GRCountX6.EichlerOptEmbCount6` in place of
  `gonzalezRotgerProp56X6`), `openResearchLeaves26S_of_26E` (`r5le := GR56.r5fpCountLe_of_eichler
  n.eichlerOptEmbCount6 t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`),
  `sixContactMin_of_open35E`, `ZInQ.Contrib.TYZChain.frozenTarget_E` (Main's frozenTarget with the new bundle).
- `lake env lean scratch/gr-dict/BypassFold.lean`: compiles; both top theorems
  `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- `BypassReach.lean` (closure of frozenTarget_E, 112698 constants; output bypass-reach.txt, VERIFIED): no
  `R5fpCount`, `GonzalezRotgerProp56X6`, `GonzalezRotgerCountX6`, `GonzalezRotgerCountX6Ab`; the count enters only
  through `GR56.r5fpCountLe_of_eichler` (EichlerOptEmbCount6) and `nocm_on_witness_le`. `GonzalezRotgerX6Ab` is
  still read by `x6Rows_of_open14_S` (via `gonzalezRotgerX6_iff_ab_gl`), i.e. the r1r2 row and X6ConicModel.
- No `shimuraTaniyamaQbar`, no `shimuraMainThmIDeligneY3AbU` used by the reroute (VERIFIED: r5fpCountLe_of_eichler's
  hypotheses are EichlerOptEmbCount6, UniformizationLeafAll, GAGAMorphism, MumfordTorsionAlgClosed).
