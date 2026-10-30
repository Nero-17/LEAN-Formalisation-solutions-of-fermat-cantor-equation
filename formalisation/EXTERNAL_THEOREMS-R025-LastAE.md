
## Standard forward irrational rotation (Kronecker)

- Lean axiom: `LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation` in `Lean/LambdaCantor/Last/ExternalKronecker.lean`.
- Statement: for irrational real alpha, every real target, epsilon>0 and natural start, there are natural k>=start and integer m with |m-alpha*k-target|<epsilon. No Cantor or Fermat hypotheses/conclusions.
- Primary source checked: John Milnor, Dynamics lecture notes, Chapter IV, section14C, Lemma14.14, PDF page index10 (printed14-11), https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf . Its forward-orbit assertion applies to any initial point; shifting the initial point gives arbitrary start and lifting the target arc gives m.
- Reason for external registration: explicitly authorized standard lemma; Mathlib AddCircle.DenseSubgroup is not cached. The corresponding Mathlib source is Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean (Yury Kudryashov,2024).
- Internal downstream proofs retained: natural k,m both escaping to infinity, arbitrary phase convergence, and actual near-axis coefficient convergence. Public IrrationalRescaling signatures unchanged. No actual source, positive dimension, or manuscript theorem is axiomatized.
- Status: source frozen, compilation pending. IrrationalRescalingAudit prints downstream axioms; update status only after actual EXIT0.

## General finite-measure Plancherel density criterion

- Lean axiom: `LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density` in `Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean`.
- Exact statement: for an arbitrary finite positive Borel measure `measure` on the real line, if its actual transform `frequency -> integral exp(-2*pi*i*frequency*point) dmeasure(point)` belongs to L2 of Lebesgue measure, there is a real density in L1 and L2, nonnegative almost everywhere, whose density measure is exactly `measure`. The squared physical L2 integral equals the squared Fourier L2 integral, with no normalization constant under the stated 2*pi convention.
- Primary sources checked 2026-10-24: Károly Simon, *Fractals and Fourier analysis*, File C, Theorem 4.3, slide83; slides84–86 give the Mattila proof and identify Mattila2015, Theorem3.3, p31: https://math.bme.hu/~simonk/ff/2017_C_8_uj.pdf . Exact unitary 2*pi normalization: Gautam Iyer, *Lecture Notes on Measure Theory*, Fall2022, section11.3, Theorem11.16, p22, with transform convention in section11.1: https://www.math.cmu.edu/~gautam/sj/teaching/2022-23/720-measure/pdfs/measure-tablet.pdf . Publisher record for the cited Mattila chapter: https://doi.org/10.1017/CBO9781316227619.004 .
- Source-to-formal specialization: dimension one; finite positive measures specialize the finite Borel criterion. Positivity of the measure makes the density nonnegative, and finiteness makes it integrable. Plancherel gives the exact norm identity. There is no parameter, Cantor, convolution, annulus, Newton, root-family, or dimension input in this axiom.
- Authorization: the user explicitly allowed precisely sourced known external general analytic tools during R025; the parent approved this exact criterion before source creation.
- Status: new optional module, source only. No active dependency-path replacement has yet been made. Existing internal Riesz/Plancherel constructions are preserved.
- Activation update: after the parent recorded the approved 18-module density-path delta in the shared project status, `AffineSobolevDensity` and `InitialKernelL2` were switched to the classical conditional-density route. Public declaration names and statements are retained. The original Riesz source modules are unchanged. `ClassicalDensityAudit.lean` checks the expected added finite-measure criterion axiom in both conditional conclusions; the source is unverified until the serial compiler and audit succeed.
- Pure definitions were separated from actual averaging: `FourierEnergyDefinition.lean` defines `fullFourierEnergy` and proves elementary Fourier measurability; the original modules reexport the same names. `FullFourierEnergy` still retains the real parameter-averaging proof imports and obligations. Thus the conditional density can be tested without assuming or deleting the manuscript's averaging estimate.

## Converse Plancherel for an actual complex L1 Fourier transform

- Lean axiom: `LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2` in `Lean/LambdaCantor/AE/ExternalPlancherelDensity.lean`.
- Exact statement: if an arbitrary complex function on the real line belongs to L1 and its actual integral Fourier transform with the 2*pi convention belongs to L2, then the original function belongs to L2 and its squared L2 integral equals the transform's squared L2 integral.
- Primary source: Iyer2022, section11.3, Theorem11.16 (bijective linear L2 isometry) together with section11.2, Theorem11.10 (inversion), at the same official CMU PDF linked above. This is the standard converse corollary: the inverse L2 transform of the given L2 transform is identified with the original L1 function by Fourier inversion and uniqueness.
- Scope: arbitrary complex L1 functions, with no support, parameter, Cantor, convolution, smoothing, root, or dimension assumptions. This may shorten the generic signed-Riesz verification path; it does not assume any manuscript interpolation estimate.
- Status: optional source only, not yet used by an active analytic module. Existing signed-Riesz source is preserved. Any active path change and downstream axiom audit must be recorded separately.

### R025 activation: generic signed Plancherel specialization in transport

Parent authorization and prior shared-status activation notice recorded before this change (2026-10-24, approximately 17:11 UTC). `ClassicalSignedDensity.classical_signed_density_memLp_and_norm_bound` specializes only the already registered general `ExternalPlancherel.complex_L1_of_fourier_L2` statement to real signed integrable functions. `SobolevTransportMollification` now calls that specialization. All actual mollifier Fourier-error, smoothing, coupling, support and scalar interpolation proofs remain formal obligations. Original `SobolevTransportSignedRiesz` and its public declarations remain in source unchanged.

The expected external analytic axiom in `ClassicalTransportAudit` is `LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2`; the separately activated affine density path retains `LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density`. No averaged-Sobolev, pair-annulus, Newton-error, root, or dimension theorem was registered. This activation is source only pending dependency-ordered compilation and axiom audit.

## Generic Newhouse Gap Lemma for binary defining sequences

- Declaration: `LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma` in `Lean/LambdaCantor/Last/ExternalNewhouseBinary.lean`.
- Primary source directly inspected: S. E. Newhouse, *The abundance of wild hyperbolic sets and non-smooth stable sets for diffeomorphisms*, Publ. Math. IHES 50 (1979), printed pp.106–108, definition of defining-sequence thickness, Lemma 4 and Remark 2. https://numdam.org/item/PMIHES_1979__50__101_0.pdf (PDF pages 6–8, zero based).
- Exact formal assumptions: two arbitrary sets of reals have explicit full binary closed-interval constructions; every node has positive width; children retain the outer endpoints and have a strict positive separating gap; the actual set equals the intersection of all finite-level unions; the interval mesh tends uniformly to zero. Each left and right child width is at least a positive bound times its node gap. The product of the two positive bounds exceeds one. Neither set lies in an order-connected subset of the other's complement, including unbounded complementary intervals.
- Conclusion: the two arbitrary sets intersect. There is no dimension conclusion, no Fermat or power/log family, and no contraction parameter in the external declaration.
- Formulation correspondence (general standard defining-sequence specialization): enumerate the finite binary node gaps ancestor first. Endpoint coherence and the strict children show these are disjoint removed gaps; exact limit equality and vanishing mesh show they exhaust the complement and give nonempty compact perfect Cantor limit sets. At a gap's removal the two adjacent bridges are the immediate children, so the explicit bounds lower-bound defining-sequence thickness. Newhouse defines set thickness as the supremum over defining sequences, with no size-order requirement. Apply Lemma 4; Remark 2 deletes the closed-gap requirement for intersection alone. The stronger finite-stage interior conclusion is deliberately absent.
- Trust boundary: only the classical general Gap Lemma is external. Actual logarithmic cylinder endpoints, exact represented set, mesh, bridge bounds, complementary-gap noncontainment, circle-gap counting and endpoint intersection witnesses must be supplied by internal Lean proofs. No such application is yet compiled or claimed.
2026-10-26 declaration-check update: ExternalNewhouseBinary.lean SHA2568266F5E0259ED231C786A9AA2DD0409F3754847C3AF42D31029303EB953E3572 actual serial compiler EXIT0 END2026-10-26T09:01:45.5135681Z (22.0675047s). Missing explicit Mathlib.Data.Real.Basic import was repaired; external proposition unchanged. This verifies declaration elaboration ONLY. Actual binary presentations/application/coarse theorem and downstream axiom audit remain pending; no upgrade to proved-paper status.

### 2026-10-27T04:37:33.8799028Z activation notice: literal Section4.7 Sobolev density wrapper

The newly integrated manuscript4.7 wrapper imports SobolevDensity and therefore AlmostEverywhereDensity. Before changing that active path, the LastAE parent authorizes this exact reuse of the ALREADY REGISTERED general ExternalPlancherel.finite_measure_L2_density proposition (same primary Simon/Mattila/Iyer sources and exact statement above). No new external proposition or internal manuscript conclusion is registered. AlmostEverywhereDensity retains all three public statements byte-for-byte; its generic exists_integrable_measure_L2_density proof simply takes the L1, L2, positivity and measure-identity components of the registered general finite-measure criterion, discarding its norm identity. The other two proofs remain unchanged.

Read-only source graph delta verified by AE owner before activation: replace ConvolutionDensity import by ConvolutionFourierL2 plus ClassicalDensityCore, keep ParameterCutoffCover. Local closure68 becomes60: remove10 old density-only modules (BoundedMeasureFunctional, ClosedBallSmoothApproximation, ConvolutionDensity, FourierTestDuality, FourierTestSubspace, MeasureFourierDuality, RepresentativeBallIntegrals, RepresentativePositivity, RieszConvolutionRepresentative, SmoothTestFourier), add ClassicalDensityCore and ExternalPlancherelDensity. All60 new-closure modules already occur in the active ActualDimensionTerminal graph; no new actual averaging/transversality/root/Newton/freezing conclusion is assumed. Old ConvolutionDensity and all Riesz source files remain unchanged. Source activation is not compiler acceptance; SobolevDensity and manuscript4.7 actual axiom audits must include the registered finite-measure criterion when used.

### 2026-10-27T05:04:32.1748069Z actual conditional-density application audit

ClassicalDensityAudit.lean SHA2565C3EC8959EE68A6FB94779168397E794204320CCEB45B7DA3BCD9DB35DAD7F57 compiled EXIT0, END2026-10-27T05:03:48.6421862Z (48.9832598s). Actual printed axiom lists for exists_common_affineSobolev_density and exists_affine_density_sharp_L2 are EXACTLY propext, Classical.choice, Quot.sound, and LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density. The Fourier density/measure identity is standard3 only. No complex converse, cylinder-extension, internal target, native or sorry axiom occurs in these three dependencies. All current-source application modules in this small chain now have canonical SHA/END/EXIT0. This verifies the previously registered conditional affine-density use; it does not certify the actual averaged energy, nonlinear centered kernel, L1 limit, full almost-everywhere dimension theorem, or new4.7 wrapper (those remain queued separately).

### 2026-10-27 actual analytic exception and irrational application audit

AnalyticSourcesAudit.lean SHA25682CC89B566DB6DEB0CBB4C1C99E8C789E23E43811392A81086B85B02E52E3A70 compiled EXIT0, END2026-10-27T14:28:06.7223938Z (48.8107395s). All eleven printed lists were read in full. two_band_affine_strict_overlap, two_band_closed_central_strict_returns, two_band_local_source_criterion and two_band_positive_derivative_criterion use exactly propext, Classical.choice and Quot.sound. real_zero_phase_depth_sequences, power_endpoint_source_positive_dimension, logarithmic_endpoint_source_positive_dimension, analytic_cubic_last_strict_upper, analytic_quadratic_last_strict_upper, analytic_three_halves_last_strict_upper and analytic_irrational_last_strict_upper use exactly those three plus the already registered general ExternalKronecker.forward_integer_difference_approximation. Its precise statement and primary Milnor source remain as registered above; no external proposition is added here. No native, sorryAx, internal conclusion or unregistered axiom appears in these lists.

The strict Section4 source-closure verifier checked2026-10-27T14:28:40Z accepts the analytic-irrational and analytic-exceptions groups with all current local SHA/END/EXIT0 dependencies. This does not establish the coarse analytic input, universal strict bound, endpoint persistence, actual nonlinear centered kernel, a.e. exact dimension or full manuscript Section4 entry; these still require their queued actual proofs and audits.

### 2026-10-27 actual four-orientation endpoint application audit

EndpointTransferAccepted.lean SHA2563866B575113A569FC54CC0025C052101D109178967C6478CADEF1B2F065D1720 compiled EXIT0, END2026-10-27T14:31:03.6644592Z. EndpointTransferCompleteAudit.lean SHA25625E6394956B9C6437EA38D9F64CF0C694F9E8FB4FF508C743FB581AD98D00EAA compiled EXIT0, END2026-10-27T14:32:17.0886125Z (45.6335883s). All five actual printed lists were read. two_band_separable_c1_criterion and two_band_positive_derivative_criterion_reciprocal use exactly propext, Classical.choice and Quot.sound. power_endpoint_source_reciprocal_positive_dimension, logarithmic_endpoint_source_reciprocal_positive_dimension and endpoint_source_positive_dimension use exactly those three plus the already registered general ExternalKronecker.forward_integer_difference_approximation. No native, sorryAx, internal conclusion or unregistered axiom appears. No new external proposition is introduced. Endpoint persistence and full Section4 integration are separate pending checks.

### 2026-10-27 actual endpoint persistence audit

EndpointTransferPersistence.lean SHA256 DD9A6C8E3A00192C65BC3001D1CFC58D226BB4F18BF6C58F2F62CB838199C9CB compiled EXIT0, END2026-10-27T14:54:10.2524475Z (35.1164785s). Its two print commands are outside the namespace so the output records full axiom names without abbreviation. endpoint_accepted_source_persists uses exactly propext, Classical.choice and Quot.sound. endpoint_source_positive_dimension_neighborhood uses exactly those three plus the already registered general LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation. Both current source-closure records are accepted by section4_acceptance.py at14:56. The earlier failed recovery prints containing sorryAx are superseded; they were never accepted. No proof statement, trust allowlist, external proposition or heartbeat option was changed by the display adjustment.

### 2026-10-27 actual open-phase C1 isolation audit

AnalyticIsolatedActualC1.lean SHA256 F184D38524F1671BCB534D6C7A4866C069A4CF768FD931BBD9076E0B6EE57B62 compiled EXIT0, END2026-10-27T15:44:20.1167252Z (30.6852094s). AnalyticIsolatedActualC1Audit.lean SHA256 B0AF2AA7DB80EE8761E17F68BEA3C1B4A2057C3DF91FED46BB94667EB4A143FF compiled EXIT0, END2026-10-27T15:45:17.1159388Z (27.2088908s). Its three actual printed dependencies for open_phase_isolated_strict_address_eventually_periodic, open_phase_isolated_strict_address_in_parameterField and open_phase_isolated_c1_point_in_parameterField are exactly propext, Classical.choice and Quot.sound. No external theorem, native axiom, sorryAx, internal conclusion axiom or unregistered proposition appears in these three lists. This records an internal proof application, not a new external result. Critical C2 and actual rational Fermat isolation audits remain separate pending checks.

### 2026-10-27 actual open/critical C2 isolation audit

AnalyticIsolatedActualPoints.lean SHA256 51E4D1B1C993C00DDA5CCA583805BFFBF48F3521CD95F9D2815A3E97FC2EAC3B compiled EXIT0, END2026-10-27T15:47:09.8301397Z (29.9699892s). AnalyticActualIsolationAudit.lean SHA256 439AA29B47D3807705967424C0B0E59229EC5B87C3EAB0884A1FE30785E744B2 compiled EXIT0, END2026-10-27T15:49:53.8508510Z (27.6128036s). Complete actual printed footprints: open_phase_isolated_c2_point_in_parameterField uses exactly propext, Classical.choice and Quot.sound; critical_isolated_c2_point_in_parameterField uses exactly those three plus the already registered generic LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering. No Mordell, native, sorryAx, internal conclusion or unregistered axiom appears in these two lists. The primary Adamczewski–Bugeaud source and exact general Pisot-stammering statement remain as registered above; no new external proposition is introduced. Actual rational Fermat isolation and the universal strict bound require the subsequent finite-generation/Mordell and return assemblies, still unverified here.

### 2026-10-27 actual rational Fermat isolation audits

RationalLastActualIsolationAbove.lean104459325C114AD626FE2C0E1433A2276113485F77C199521972CEB466A1B159 passed END15:58:16.8715189Z. AboveAudit2E333BA0E5822239726B16D24D3E213D385EE166C9DA76E1A9863984A9B9A1CB passed END15:59:59.0562986Z. Actual coordinate classification above the critical ratio uses exactly standard3; actual isolated-point finiteness above critical uses standard3 plus registered External.mordell_smooth_plane_curve only.

RationalLastActualIsolationNormalized57FB2CAA491631FDF1D0FDDA2D6FDE2137993DB5C41CB3ACC8843BCA1646F318 passed END16:01:28.1568211Z. ActualIsolationFermat passed END16:02:54.8235474Z. ActualIsolationAudit387B051C1AF6C2680D5A615FD073A02C060C55DC37DD91D7D137E52983122CC8 passed END16:03:51.3129983Z (28.2522039s). Its four actual lists were read completely: exists_actual_fermat_prefix_normalization and normalizedFermatPrefix_isolated_pullback are exactly standard3; actual_rational_fermat_isolated_coordinates_at_critical is standard3 plus the registered general AB Pisot-stammering result; finite_isolated_actual_rational_intersection_at_critical is standard3 plus that result and the registered general Mordell theorem. No native, sorryAx, internal conclusion or unregistered axiom occurs. No external proposition is added here. The strict full local source-closure verifier at16:06 accepts the analytic-isolated group including these actual discharges; full Section4 still requires coarse/returns/universal and AE/manuscript integration.


### 2026-10-27T16:50:21.015383+00:00 universal strict last bound: complete actual terminal receipt
Frozen manuscript commit:429d53bb243f49b19ba8169de0e82ed70050ec7f. Public theorem: `LambdaCantor.Last.universal_lastTransition_lt_critical {exponent : ℝ} (hexponent : 1 < exponent) : lastTransition exponent < (Real.sqrt 3 - 1) / 2`. No caller hypotheses beyond the real exponent being greater than one; reduced rational representation, three small exceptional cases, actual infinitude, actual finite isolation and return persistence are discharged internally. This does not certify the separate a.e. dimension/Sobolev/sqrt2 pipeline or integrated Section4 entries.

**RationalLastStrictAudit.lean** SHA256 `85C2530D352501C4D0C36405DA3429C25F831F9D7D7BBF21FFD1176F2F60C7BB`, END_UTC `2026-10-27T16:26:21.3515909Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.selected_perfect_actual_fermat_normalization`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.strict_return_criterion_persist_parameter`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.joint_strict_derivative_moving_cylinder_error`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.perfect_fibre_positive_dimension_persist_parameter`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.actual_fermat_positive_dimension_persist_of_infinite_of_finite_isolated`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.rational_positive_dimension_at_or_above_critical_of_infinite`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical_of_infinite_intersections`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve`.

**AnalyticCoarseConclusionAudit.lean** SHA256 `7F74D6846092BDF95717E766CF99C4471FBA453BFE4A1761CE407E96AD6DCC3B`, END_UTC `2026-10-27T16:28:26.7366312Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.coarse_strict_log_link_all_exponents`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.coarse_rational_infinite_intersection`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

**UniversalLastAudit.lean** SHA256 `744BB607CE407DBD48153859776E245F22A4AFCB0974270595C156A97637E1D5`, END_UTC `2026-10-27T16:34:33.4885358Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.analytic_irrational_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_quadratic_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_cubic_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.analytic_three_halves_last_strict_upper`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation`.
- `LambdaCantor.Last.coarse_strict_log_link_all_exponents`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.coarse_rational_infinite_intersection`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.rational_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.universal_lastTransition_lt_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

**UniversalLastPositivity.lean** SHA256 `7C92E3128878161A7E6CF9D12CB68BA9B4F8367DF5FF8FF603C307C2ED334A6E`, END_UTC `2026-10-27T16:41:02.6105479Z`, EXIT0. Every actual printed list:
- `LambdaCantor.Last.positive_dimension_above_lastTransition`: `propext, Classical.choice, Quot.sound`.
- `LambdaCantor.Last.universal_positive_dimension_at_or_above_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.
- `LambdaCantor.Last.universal_positive_dimension_near_critical`: `propext, Classical.choice, Quot.sound, LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering, LambdaCantor.Last.External.mordell_smooth_plane_curve, LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation, LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma`.

The universal strict theorem uses exactly the three ordinary Lean foundations plus these FOUR already registered generic classical inputs, and no others:
- Kronecker forward irrational approximation: Milnor, Dynamics notes IV14C, Lemma14.14, https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf .
- Adamczewski–Bugeaud, Annals165 (2007), Theorem5 pp553–554, the precisely registered Pisot/exact-double stammering specialization: https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf . Exact Lean statement and source check: EXTERNAL_SOURCE_CHECKS-R025-Root.md.
- General Mordell over finitely generated characteristic-zero fields, smooth plane-curve specialization: Jarden–Razon, Proposition5.2, https://www.math.tau.ac.il/~jarden/Articles/paper60.pdf . Exact Lean statement and source check: EXTERNAL_SOURCE_CHECKS-R025-Root.md.
- Generic Newhouse binary defining-sequence gap lemma with actual bridge/thickness/linking hypotheses: Newhouse1979 printed pp106–108, Lemma4/Remark2, https://numdam.org/item/PMIHES_1979__50__101_0.pdf . Exact statement and scope are registered earlier in this file.
No internal paper conclusion, Fourier-density/projection input, native axiom, sorryAx or unregistered theorem occurs in the universal strict theorem's actual footprint. The five purely geometric/normalization return heads use only standard3; the exact per-head differences are recorded above. No new external proposition is introduced by this receipt.
UniversalLastPositivity's only post-pass modification was adding these three diagnostic print commands outside its namespace; all theorem bodies/signatures are unchanged, the new SHA has now itself compiled EXIT0, and all three printed footprints are recorded above. UniversalLastConclusion and UniversalLastAudit remain frozen at their accepted SHAs.


2026-10-27T18:55:34.683897+00:00 Actual norm-convention comparison receipt (no new external proposition)
Sole scope: all real regularity>=0 and every real frequency, including both zero endpoints; standardWeight <= 2^regularity * implementedWeight and implementedWeight <= 2 * standardWeight. Constants are independent of ratio/frequency. This does not alone prove averaged Sobolev4.7 or canonical compact integrability.

UTC=2026-10-27T18:52:36.4796208Z MODULE=LambdaCantor/AE/SobolevWeightComparison.lean SHA256=8DF52E47CB9C80506BB82D0E7A3A78A934A789E45C609D9F8555ECCDA296F625
'LambdaCantor.AE.sobolev_weight_comparison_standard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.sobolev_weight_comparison_implemented_le' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED_SECONDS=35.4056241 END_UTC=2026-10-27T18:53:11.8879452Z
EXIT=0



2026-10-27T19:59:50.763786+00:00 Actual canonical and averaged Sobolev core: complete15-list receipt
Scope: actual Cantor self-convolution, actual nonnegative L1-and-L2 density, exact density/measure Fourier identity, canonical weight(1+abs(frequency)^2)^regularity; every compact subset of an admissible interval has finite extended-valued canonical parameter energy and integrable toReal. Conditions0<lower<=upper<1/2, regularity>=0 and exact2*regularity<2*log(8/3)/log(upper/lower^3)-1. Old extended parameter integral is recovered from independently proved AE energy<top before integrable_toReal_iff; infinity.toReal cannot hide an infinite parameter-energy contribution. These are core conclusions; the literal wrapper and all Section4/integrated entries still need their actual certificates.
Every comparison/compact-integral head uses exactly standard3. The AE density heads add ONLY the already registered generic ExternalPlancherel.finite_measure_L2_density, whose precise finite-measure/Fourier-L2 statement and sources are in the existing external registers/AE/ExternalPlancherelDensity.lean. No new external proposition/native/sorry/internal-paper conclusion axiom.

UTC=2026-10-27T19:52:37.2280450Z MODULE=LambdaCantor/AE/CanonicalSobolevEnergy.lean SHA256=450C9BA5DB8B478B35B58D46623634DA57DD06021A200443EA2C537FA322971A
'LambdaCantor.AE.canonicalSobolevEnergy_le_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_le_canonicalSobolevEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.integrableOn_canonicalSobolevEnergy_compact_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.ae_hasCanonicalSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=47.9860456 END_UTC=2026-10-27T19:53:25.2191566Z
EXIT=0


UTC=2026-10-27T19:54:20.5240684Z MODULE=LambdaCantor/AE/AveragedSobolevAudit.lean SHA256=A7778A272218BF2785D5DD58E4A8E100199CADEBE2B69B07D97EE407DE4D5482
'LambdaCantor.AE.lintegral_cutoff_fullFourierEnergy_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.locallyIntegrableOn_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_eq_convolution_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fourier_density_eq_measureFourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.ae_hasSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
'LambdaCantor.AE.canonicalSobolevEnergy_le_fullFourierEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.fullFourierEnergy_le_canonicalSobolevEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'LambdaCantor.AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.integrableOn_canonicalSobolevEnergy_compact_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LambdaCantor.AE.ae_hasCanonicalSobolevDensity_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=41.0337524 END_UTC=2026-10-27T19:55:01.5600530Z
EXIT=0



Literal frozen Lemma4.7 independent wrapper accepted receipt; exactstatementB84 scope ownerchecked against frozenmain.tex2201-2208. Diagnostic-only namespace relocation from7EF preserves proof/statement; newactualfullqualified footprint (no whitelist relaxation):
UTC=2026-10-27T20:15:57.1971587Z MODULE=LambdaCantor/Manuscript/AverageSobolev.lean SHA256=BD27FC7C8B1A00222AF21B4364C4427DD950A4092E9F3987B7162575A7DCE6BC
'LambdaCantor.Manuscript.average_sobolev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density]
ELAPSED_SECONDS=32.0497597 END_UTC=2026-10-27T20:16:29.2684100Z
EXIT=0

Full16group goal andcompleteSectionFour/fivehead totalentry stillrequired; this receipt alone does not certifyAEexactdimension orsqrt2.

2026-10-28T05:02:55.1801114Z Actual general transport three-head receipt
Scope: the actual signed-density Plancherel norm bound, the actual mollification L2/error-energy estimate, and the actual sharp L1 smoothing/coupling transport inequality for arbitrary probability densities on a compact interval. The last theorem preserves the actual coupling cost and exact regularity/(1+regularity) exponent. Current source SobolevTransport116D12658938585F157D4F95E472F12678B2013EA55F4E223C09BFB7B05F20AB passed END04:54:58.6061814Z/200.0552723s/EXIT0; the diagnostic audit below is itself current-source EXIT0.
Every one of the three full actual axiom lists is exactly standard3 plus the already registered generic ExternalPlancherel.complex_L1_of_fourier_L2. No new proposition/axiom, native arithmetic, sorryAx, internal paper conclusion, or kernel/root-mass premise was introduced. The generic input concerns an actual complex L1 function whose actual Fourier transform is in L2, with the exact Plancherel norm identity for the exp(-2*pi*i*x*frequency) convention; exact unchanged Lean statement and primary-source registration are in AE/ExternalPlancherelDensity.lean48 and the earlier register. Primary source: Gautam Iyer, Lecture Notes on Measure Theory (2022), section11.3, Theorem11.16, plus Fourier inversion/uniqueness as already registered: https://www.math.cmu.edu/~gautam/sj/teaching/2022-23/720-measure/pdfs/measure-tablet.pdf . This receipt certifies these actual analytic heads only; complete actual AE exact dimension/sqrt2/final entries remain required.

UTC=2026-10-28T05:01:01.4188631Z MODULE=LambdaCantor/AE/ClassicalTransportAudit.lean SHA256=BFD7E4CD7E29D7F35B50497F7F32289A8AFDD267608078DA88FACCE79A9960FB
'LambdaCantor.AE.classical_signed_density_memLp_and_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2]
'LambdaCantor.AE.mollification_error_memLp_and_energy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2]
'LambdaCantor.AE.exists_density_transport_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2]
ELAPSED_SECONDS=113.7322006 END_UTC=2026-10-28T05:02:55.1801114Z
EXIT=0



## 2026-10-28T22:04:24.394151+00:00 Actual full Section4 sixteen-group receipt

All original 16 requirement groups, seven integrated heads and five manuscript wrapper heads now have current-source EXIT0 and fresh transitive source closure; no unknown, native or sorry axiom occurs in these terminal lists. This is a compiler/statement/source audit receipt, not a claim that external classical theorems were proved internally, the whole First/Main/article task is done, or Drive was updated. No trust allowlist or public mathematical statement was weakened.

The local admissible-band declaration was originally required as well as the full interval declaration. Its missing print was supplied by a new import-only AE/ActualDimensionTerminalAudit module while freezing the already passed mathematical source. Both original declarations remain mandatory; the requirements count stays16.

Actual current receipts (full raw prints retained):

[
  {
    "module": "LambdaCantor/AE/ActualDimensionTerminal.lean",
    "source_sha": "59CA4F40E7810C075894C622DABF396B8C31FFF09C7170FF6713E159FC03F75C",
    "end_utc": "2026-10-28T21:44:25.7237961Z",
    "actual_prints": {
      "LambdaCantor.AE.irrational_ae_dimension_equality": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2"
    }
  },
  {
    "module": "LambdaCantor/AE/ActualDimensionTerminalAudit.lean",
    "source_sha": "91B484939F801D1173D50705134D85E91DE836E754264A164C6C3D55422522C0",
    "end_utc": "2026-10-28T21:57:13.3264839Z",
    "actual_prints": {
      "LambdaCantor.AE.ae_dimension_equality_on_actual_admissible_band": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2"
    }
  },
  {
    "module": "LambdaCantor/Last/ActualSectionFour.lean",
    "source_sha": "B7165368B9DBE9EAF4C8983C21F5B9935FD226C00CB49E6E11D1F57B0C84E723",
    "end_utc": "2026-10-28T21:56:16.4523231Z",
    "actual_prints": {
      "LambdaCantor.Last.two_band_separable_c1_closed_interval_criterion": "propext,\n Classical.choice,\n Quot.sound",
      "LambdaCantor.Last.universal_lastTransition_lt_critical": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering,\n LambdaCantor.Last.External.mordell_smooth_plane_curve,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma",
      "LambdaCantor.Circle.circle_positive_measure": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2",
      "LambdaCantor.Circle.circle_onset": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2",
      "LambdaCantor.Circle.circle_zero_intervals": "propext, Classical.choice, Quot.sound",
      "LambdaCantor.Circle.circle_known_separation": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2",
      "LambdaCantor.AE.irrational_ae_dimension_equality": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2"
    }
  },
  {
    "module": "LambdaCantor/Manuscript/SectionFour.lean",
    "source_sha": "7287CF7CD77A54F97B7DD3E2DA45F4617511AE37A716EB4143F28E1395635EC9",
    "end_utc": "2026-10-28T21:58:07.5960754Z",
    "actual_prints": {
      "LambdaCantor.Manuscript.introductory_last_transition": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering,\n LambdaCantor.Last.External.mordell_smooth_plane_curve,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma",
      "LambdaCantor.Manuscript.introductory_ae_dimension": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2",
      "LambdaCantor.Manuscript.average_sobolev": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density",
      "LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2"
    }
  },
  {
    "module": "LambdaCantor/Last/SectionFourManuscriptAudit.lean",
    "source_sha": "9810BD7316F63E2569C08F24F83C7B9C400CE176FA65B3CCADB87B7C4AEA78B5",
    "end_utc": "2026-10-28T21:59:01.6748039Z",
    "actual_prints": {
      "LambdaCantor.Manuscript.introductory_last_transition": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.Last.External.adamczewski_bugeaud_pisot_stammering,\n LambdaCantor.Last.External.mordell_smooth_plane_curve,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.Last.ExternalNewhouse.binary_defining_sequence_gap_lemma",
      "LambdaCantor.Manuscript.introductory_ae_dimension": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2",
      "LambdaCantor.Manuscript.average_sobolev": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density",
      "LambdaCantor.Manuscript.expectedDimension_strictly_increasing": "propext,\n Classical.choice,\n Quot.sound",
      "LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds": "propext,\n Classical.choice,\n Quot.sound,\n LambdaCantor.AE.ExternalPlancherel.complex_L1_of_fourier_L2,\n LambdaCantor.AE.ExternalPlancherel.finite_measure_L2_density,\n LambdaCantor.First.ExternalProjection.shmerkin2019_theorem62_four_maps,\n LambdaCantor.First.LinearRegularity.falconer2003_product73_interval,\n LambdaCantor.First.LinearRegularity.shmerkin2014_proposition23_two_maps,\n LambdaCantor.First.LinearRegularity.shmerkin2019_theorem92_uniform_l2,\n LambdaCantor.Last.ExternalKronecker.forward_integer_difference_approximation,\n LambdaCantor.First.Roots.External.classical_compact_measure_l2_fourier_density,\n LambdaCantor.First.Roots.External.classical_plancherel_l1_l2"
    }
  }
]

Source and specialization review of the actual AE footprint:

- Existing general Milnor irrational rotation input: actual Last/ExternalKronecker.lean:14 allows any irrational real, any target, epsilon>0 and arbitrary natural start, with the second index integer. Milnor chapterIV, Lemma14.14, printed14-11 / PDF index10, states density of every forward irrational rotation orbit. Shifting the initial point gives the start bound; lifting the target arc gives the integer. Primary reread: https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf . This has no Cantor/Fermat conclusion.
- Existing First compact-measure Fourier converse: RootsFourierDensityInterface.lean:19–22 requires a finite positive real-line measure, actual compact support and MemLp(charFun measure)2. HasL2Density at LinearRegularityExternal.lean:41–44 means a measurable nonnegative L1/L2 density with the measure identity; it does not impose probability mass1. Roman Garcia arXiv1801.09022v3 Theorem1.2(1), printed2 / PDF index1, directly covers compact positive finite Radon measures. Its Fourier convention differs from charFun by fixed nonzero frequency/reflection/amplitude scaling, preserving L2 membership. Primary reread: https://arxiv.org/pdf/1801.09022 . No sharp norm constant is added to this First converse.
- Existing First forward Plancherel: RootsExternalPlancherel.lean:27–33 requires complex L1 intersect L2 and concludes L2 membership of the actual integral transform and equality of squared norms. Tao 247B Notes1 equations(1),(3) use exactly exp(-2*pi*i*x*frequency), matching mathlib Real.fourierChar/inner product. Primary reread: https://terrytao.wordpress.com/2020/03/29/247b-notes-1-restriction-theory/ .
- Existing AE Plancherel pair: ExternalPlancherelDensity.lean:40–52 retains Fourier MemLp2, not merely a real integral that could vanish on nonintegrable functions. ConvolutionMeasureCore.lean:29–30 is the actual exp(-2*pi*i*frequency*value) convention. Iyer2022 section11.2 Theorem11.10 and section11.3 Theorem11.16 were reread at https://www.math.cmu.edu/~gautam/sj/teaching/2022-23/720-measure/pdfs/measure-tablet.pdf . The complex L1 converse is a corollary of L2 Plancherel plus distributional Fourier uniqueness, not a verbatim theorem11.16 statement. For the general finite-measure density criterion the prior Simon/Mattila registration remains; the Simon slide URL failed this fresh retrieval and is not represented as freshly read. Its general finite-measure scope can also be checked by the standard Schwartz-test duality: Fourier inversion and finite-measure Fubini bound the measure functional on L2 by the Fourier L2 norm; L2 Riesz representation gives the density, positivity/finiteness give nonnegativity and L1, and Plancherel gives the exact norm identity. This is a stated classical corollary argument, not a new internal Lean proof or newly registered axiom.
- Reused Sol/high agent read the full actual First external types and their auxiliary definitions, matched the current First register, and compared primary texts for the remaining four entries. ExternalProjection.lean:52 is the four distinct equal-atom exponential-separation specialization of Shmerkin2019 Theorem6.2, printed368. LinearRegularityExternal.lean:56 is Theorem9.2 with two parameters and q=2, retaining positive contractions, analytic connected open domain, infinite-address nondegeneracy and strict atomic q-mass condition; it claims no uniform L2 norm. Primary publisher PDF: https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf .
- LinearRegularityExternal.lean:79 is the two-fair-map specialization of Shmerkin2014 Proposition2.3. Its zero-dimensional contraction exception is independent of translations, and measure-dependent Fourier decay constants absorb the published exp(i*pi*frequency*x) versus charFun exp(i*frequency*x) scaling: https://arxiv.org/html/1303.3992v2#S2.SS2.Thmproposition2.3 .
- LinearRegularityProduct.lean:25 is Falconer2003 formula7.3 with a compact interval as second factor; its upper box dimension is at most1, with no measurability/boundedness assumption on the first factor. Product max and Euclidean metrics are bi-Lipschitz equivalent. Source: printed102/PDF128, https://www.muslimuniversity.edu.af/uploads/library/Fractal.Geometry.Mathematical.Foundations.and.Applications.Second.Edition.eBook-EEn_957.pdf ; publisher https://doi.org/10.1002/0470013850.ch7 . The agent verified PDF text; screenshot and publisher DOI access failed, so no visual PDF verification is claimed.

These reviews found no concrete unsupported strengthening and no axiom directly asserting the internal Section4 Fermat/Cantor conclusion. Limits: these remain explicitly allowed sourced external classics, not newly internalized proofs; the source review is separate from the actual completed Lean application checks. Earlier source-only statuses and failed prints are historical and do not override these successful receipts. The original statements and prior conditional proofs remain in source; only the new actual construction closes the former caller-kernel/full-mass gap.
