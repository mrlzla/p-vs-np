# P versus NP research workspace

The research target is deterministic worst-case polynomial time for encoded 3-SAT. Lean checks the equivalence with P = NP in the pinned Cook–Levin development, and separately checks the gate-by-gate encoding used to measure what the October 2026 SAT algorithms can do for circuits. The Clay Mathematics Institute lists P versus NP as unsolved. [Clay problem statement](https://www.claymath.org/millennium/p-vs-np/)

## Build and inspect

On `vladartemyev@192.168.0.128`, the workspace is `~/Documents/math/p-vs-np`. It pins Lean and Mathlib 4.35.0 and `NPComplete` 0.5.0. Run from the workspace root with elan on `PATH`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
lake env lean --stdin <<'EOF'
module
import PvsNP
#print axioms PvsNP.p_eq_np_iff_threeSat_in_p
#print axioms PvsNP.p_ne_np_iff_threeSat_not_in_p
#print axioms PvsNP.Circuit.acceptingAssignmentsEquiv
#print axioms PvsNP.Circuit.acceptingAssignmentsByBoundary
#print axioms PvsNP.Circuit.wire_count
#print axioms PvsNP.Circuit.encode_size
#print axioms PvsNP.Circuit.encode_width
#print axioms PvsNP.or_requires_wide_clause
EOF
```

- [Problem.lean](PvsNP/Problem.lean) reuses Cook–Levin to express both sides of the open problem in a binary-encoded TM0 model. The target is 3-SAT on the library's valid 3-CNF inputs. [Pinned Cook–Levin development](https://github.com/starpos/lean-np-complete/tree/v0.5.0)
- [CircuitCNF.lean](PvsNP/CircuitCNF.lean) uses Lean's `Std.Sat.CNF` for the Tseitin encoding. An $n$-input circuit with $s$ AND, OR or NOT gates has $n+s$ declared wire variables, at most $3s+1$ clauses and width at most 3. The assignment bijection gives exact count preservation over all declared wires, and conditioning on selected wires partitions the accepting inputs into disjoint branches. With an endpoint that counts only occurring variables, multiply its count by $2^u$ for the $u$ unused declared variables. The local file establishes semantic correctness and structural size. Encoded machine-time results for the analogous compilation are available in the frontier library. [Existing circuit counting formalization](https://github.com/cslib-community/cslib-frontier/blob/6a5fb39b1da33ce1f41adf0f9b234982e48e33ef/Complexity/Computability/Complexity/FineGrained/CircuitCounting.lean)
- `or_requires_wide_clause` gives an obstruction to eliminating auxiliary variables. A CNF that expresses OR directly on its $n$ inputs requires a clause of width at least $n$.

The literature review, exponent calculation and proposed research milestones are in [RESEARCH.md](RESEARCH.md).

## Direct P versus NP target

[MCSPTarget.lean](frontier/MCSPTarget.lean) imports the existing hardness magnification theorem in CSLib Frontier and states a concrete lower bound sufficient for $P\ne NP$. Check it with the pinned frontier checkout on the server. Its toolchain is Lean 4.36.0-rc2.

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd ~/Documents/math/eth-sources/complexitylib
lake build Complexity.Computability.MCSP.Magnification
lake env lean ~/Documents/math/p-vs-np/frontier/MCSPTarget.lean
```

[MCSPRestrictions.lean](frontier/MCSPRestrictions.lean) proves a lower bound at cutoff $m^2$ in the same circuit model. For $N=2^m$ and $b=\lfloor\log_2(m+1)\rfloor+1$, put $B=4b+(3+4b)m^2$. The restriction argument gives $G_2(m)\ge N-1-B$. Accounting for the certificates of the all-zero and all-one truth tables improves this to $G_2(m)\ge 2N-1-2B$. For $m=16$, the checked lower bound is 119,255 gates. See the [argument and its scope](RESEARCH.md#checked-mcsp-lower-bound).

```sh
lake build Complexity.Computability.Circuit.Support Complexity.Computability.Circuit.Boolean.Hierarchy
lake env lean -DwarningAsError=true ~/Documents/math/p-vs-np/frontier/MCSPRestrictions.lean
```

The [many-certificate experiment](RESEARCH.md#many-accepted-tables) adds a gate accounting inequality for arbitrary samples, an accepted projection family, and circuits that recognize exactly any prescribed finite sample. From the same frontier checkout, run

```sh
toolchain=$(cat lean-toolchain)
frontier="$HOME/Documents/math/p-vs-np/frontier"
export LEAN_PATH="$frontier/.lake:$(lake env printenv LEAN_PATH)"
cd "$frontier"
mkdir -p .lake
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPRestrictions.olean MCSPRestrictions.lean
elan run "$toolchain" lean -DwarningAsError=true MCSPMultiCertificates.lean
elan run "$toolchain" lean -DwarningAsError=true MCSPSampleControls.lean
```

[MCSPCommunicationCut.lean](frontier/MCSPCommunicationCut.lean) gives a balanced input partition for quadratic-cutoff MCSP at arity 32 that forces at least 512 crossing wires for every placement of the gates. See the [cut argument](RESEARCH.md#communication-cut). With the same toolchain and `LEAN_PATH` as above, check it with `elan run "$toolchain" lean -DwarningAsError=true MCSPCommunicationCut.lean`.

[MCSPNarrowCut.lean](frontier/MCSPNarrowCut.lean) gives a control whose minimum circuit uses at most $2N-1535$ gates at arity 32 and still requires 512 crossing wires on every mask in the family. The control matches the equality probes and the sparsity bound. See the [narrow-cut test](RESEARCH.md#narrow-cut-test). From the same directory and environment, run

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPCommunicationCut.olean MCSPCommunicationCut.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPSampleControls.olean MCSPSampleControls.lean
elan run "$toolchain" lean -DwarningAsError=true MCSPNarrowCut.lean
```

[MCSPPairWiring.lean](frontier/MCSPPairWiring.lean) transfers split-pair swap invariance to a direct gate-wiring constraint. [MCSPSplitControl.lean](frontier/MCSPSplitControl.lean) tests that constraint with a minimum-circuit control that also accepts the split projection and stays wide on every good mask. See the [orientation and wiring test](RESEARCH.md#orientation-and-wiring). Check both from the same Lean environment with

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPNarrowCut.olean MCSPNarrowCut.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPPairWiring.olean MCSPPairWiring.lean
elan run "$toolchain" lean -DwarningAsError=true MCSPSplitControl.lean
```

[MCSPRefinedProbeControl.lean](frontier/MCSPRefinedProbeControl.lean) and [MCSPRefinedProbeSplices.lean](frontier/MCSPRefinedProbeSplices.lean) construct a tail-permutation-invariant control at arity 32 (`N = 2^32`) that accepts all transported refined probes, agrees with `mcspSquare 32` on all transported diagonal and mixed splices of a shared anchored selector (`common_transport_test`), and uses at most $2N - 535{,}095{,}901$ gates (`control_size`) by relaxing sparsity (`accepted_count_lower`). See the [refined-probe control analysis](RESEARCH.md#refined-probe-control-and-transported-mixed-splices).

[MCSPTwoCornerStructure.lean](frontier/MCSPTwoCornerStructure.lean), [MCSPMonotoneForest.lean](frontier/MCSPMonotoneForest.lean), and [MCSPSuperTwoN.lean](frontier/MCSPSuperTwoN.lean) formalize the two-corner gate classification, the monotone OR/AND forest decomposition and Two-Corner Bottleneck Ledger (`eval_eq_of_cutInputs_and_roots`, `cutInputs_perturbation_invariant`, `clean_case2_structure`), the bottleneck fooling bound (`bottleneck_fooling_card_le`), and the sharpened unconditional super-$2N$ De Morgan circuit size lower bounds for `mcspSquare m` (`mcspSquare_super_twoN`, `mcspSquare_32_gt_twoN`) and for sparse circuits accepting the refined-probe patterns (`sparse_pattern_super_twoN`). See [two-corner gate structure and super-2N lower bounds](RESEARCH.md#two-corner-gate-structure-monotone-orand-forest-and-super-2n-lower-bounds). Replay them from the frontier environment on `vladartemyev@192.168.0.128`:

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPTwoCornerStructure.olean MCSPTwoCornerStructure.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPMonotoneForest.olean MCSPMonotoneForest.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPSuperTwoN.olean MCSPSuperTwoN.lean
```

[MCSPMinimumAliases.lean](frontier/MCSPMinimumAliases.lean), [MCSPMinimumAliasControl.lean](frontier/MCSPMinimumAliasControl.lean), and [MCSPFreshBypass.lean](frontier/MCSPFreshBypass.lean) bound early stop-gate aliases by `changedGates` under circuit minimality (`minimum_early_readers_card_le`), give minimum forest-masked controls where pinning produces an early stop alias (`minimum_has_early_stop_reader`) and where an unhit escaping forest root hides the extra fresh bypass outside `StopGate` (`escape_stop_losses_card`, `escape_fresh_losses_ge_two`), and eliminate the `StopGate` restriction and early-alias term $A$ by charging over all `fresh` gates (`match_fresh_oriented_readers`, `mcsp_affine_fresh_oriented_charge`, `binate_full_support_lower`). See [minimum-circuit alias control and fresh bypass readers outside stop gates](RESEARCH.md#minimum-circuit-alias-control-and-fresh-bypass-readers-outside-stop-gates). Replay them after building the prerequisite `.lake/*.olean` modules on `vladartemyev@192.168.0.128`:

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPMinimumAliases.olean MCSPMinimumAliases.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPMinimumAliasControl.olean MCSPMinimumAliasControl.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPFreshBypass.olean MCSPFreshBypass.lean
```

[MCSPEarliestFresh.lean](frontier/MCSPEarliestFresh.lean) discharges the `hJoint` wiring hypothesis and circuit minimality via the earliest `fresh` gate on effective masks (`effMask`), proving the unconditional dichotomy (`earliest_fresh_double_loss_or_funnel`), the $2(n - B - 1)$ funnel-free lower bound (`adaptive_eff_noFunnel_bound`), the exact `mcspSquare m` ($m \ge 7$) reduction to ruling out affine controlling pair funnels (`mcspSquare_earliest_fresh_dichotomy`, `mcspSquare_noFunnel_twoN`), and the parametric `blockAtMostOne` sharpness counterexample (`blockAtMostOne_beats_twoN_at_8_8`, complexity $\le 77 < 102$ at $K = 8, b = 8$). See [discharging the joint-reader hypothesis: earliest fresh gates and pair funnels](RESEARCH.md#discharging-the-joint-reader-hypothesis-earliest-fresh-gates-and-pair-funnels). Replay it after building the prerequisite `.lake/*.olean` modules on `vladartemyev@192.168.0.128`:

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPEarliestFresh.olean MCSPEarliestFresh.lean
```

[MCSPPairFunnelGap.lean](frontier/MCSPPairFunnelGap.lean) formalizes exact De Morgan circuit duality (`mcspSquare_dualTable`) to exclude complementary pair funnels (`mcspSquare_no_comp_funnel`), proves the $S_m$-stabilizer orbit bound excluding large-orbit unpinned funnels (`mcspSquare_funnel_orbit_le`, `mcspSquare_32_no_weight5_zero_funnel`), and constructs the affine-invariant `affineBlockAtMostOne` barrier (`affineBlockAtMostOne_barrier_at_14`, `affineBlockAtMostOne_barrier_at_32`) showing that affine tables, 1-bit affine flips, sparsity, and nonconstant 1-bit branches admit an essential `IsPairFunnel` with residual complexity $\approx 1.03 N$ after pinning $3(m + 1)$ bits. See [pair-funnel exclusion under symmetry and the affine-basis funnel barrier](RESEARCH.md#pair-funnel-exclusion-under-symmetry-and-the-affine-basis-funnel-barrier). Replay it after building `.lake/MCSPEarliestFresh.olean` on `vladartemyev@192.168.0.128`:

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPPairFunnelGap.olean MCSPPairFunnelGap.lean
```

[MCSPQuadraticForest.lean](frontier/MCSPQuadraticForest.lean) breaks the affine 2-plane averaging bottleneck using rank-1 quadratic probes (`quad`, `complexity_quad_le`, `mcspSquare_accepts_quad`, `patched_quad_accepted`) with uniform $\frac{1}{4}$ averaging (`card_quad_const_mul_le`) and zero $+2N$ linear penalty (`exists_reindexed_quad_forest_mask_witness`). Combined with the **12.8×** two-corner and monotone-forest slack tightening across [MCSPTwoCornerStructure.lean](frontier/MCSPTwoCornerStructure.lean) (`sharedBool`, `twoCorner_tight_bundle`, `dualOtherBad`) and [MCSPMonotoneForest.lean](frontier/MCSPMonotoneForest.lean) (`card_stopInputs_and_roots_le_tight`: $6B + 112\,\mathrm{slack}$ vs $10B + 1438\,\mathrm{slack}$), this yields slope $281/280$ (`quad_reindexed_forest_size`, `mcspSquare_quad_super_twoN`) and establishes unconditional $m = 32$ De Morgan circuit lower bounds of **$8{,}620{,}555{,}905$** gates from the pure forest (`mcspSquare_32_quad_forest`) and **$8{,}620{,}555{,}922$** gates with 17 minority-pinning losses (`mcspSquare_32_quad_minority`, +28,287,454 over $8{,}592{,}268{,}468$). See [rank-1 quadratic probes break the affine 2-plane bottleneck](RESEARCH.md#rank-1-quadratic-probes-break-the-affine-2-plane-bottleneck) and [polarity-disjoint sharing, segment-bottom cancellation, and the 8,620,555,922 bound](RESEARCH.md#polarity-disjoint-sharing-segment-bottom-cancellation-and-the-8620555922-bound). Replay the updated chain on `vladartemyev@192.168.0.128`:

```sh
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPTwoCornerStructure.olean MCSPTwoCornerStructure.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPMonotoneForest.olean MCSPMonotoneForest.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPSuperTwoN.olean MCSPSuperTwoN.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPMinorityResidual.olean MCSPMinorityResidual.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPQuadraticForest.olean MCSPQuadraticForest.lean
elan run "$toolchain" lean -DwarningAsError=true -o .lake/MCSPPolynomialBarrier.olean MCSPPolynomialBarrier.lean
```

[MCSPMinimumForestAbsorption.lean](frontier/MCSPMinimumForestAbsorption.lean) combines the physical port count with pins chosen from the actual clean forest. The exact arity-32 MCSP lower bound is **8,630,800,316 gates** (`mcsp32_absorbing_block_floor_ports`). See [physical ports and corner-specific cut endpoints](RESEARCH.md#physical-ports-and-corner-specific-cut-endpoints).

[MCSPPolynomialBarrier.lean](frontier/MCSPPolynomialBarrier.lean) formalizes the bounded-degree $\mathbb{F}_2$-polynomial (Reed–Muller) barrier against our $O(N)$ MCSP techniques: `isDeg d m` satisfies full $\mathrm{AGL}(m,\mathbb{F}_2)$ (`isDeg_agl_invariant`) and De Morgan duality (`isDeg_dualTable`) invariance, exact sparsity $2^{\mathrm{rmDim}\,2\,m} \le 2^{B(m)}$ (`card_accepting_isDeg2_le_mcspBound`), and accepts all rank-1 quadratic probes (`isDeg_two_accepts_quad`), yet computes exact degree $\le d$ in linear De Morgan circuit size (`complexity_isDeg2_le`: $\le 10N + m^2$) and linear De Morgan formula leaf size (`formulaSize_isDeg2_le`: $\le 32N$), pinning `isDeg 2 32` inside $[8{,}620{,}611{,}839,\, 42{,}949{,}673{,}984]$ gates (`isDeg2_32_bracket`) and exhibiting explicit non-polynomial separation witnesses (`pointFn`, `monomial3`, `isDeg_prefix_probe_sep_32`). See [the bounded-degree polynomial barrier](RESEARCH.md#the-bounded-degree-polynomial-barrier-and-the-862b-4295b-bracket).

In `pequalnp/proposals/`, [L_meta_060.lean](pequalnp/proposals/L_meta_060.lean) and [L_meta_066.lean](pequalnp/proposals/L_meta_066.lean) provide local contribution proofs for Brilliant's `PEqualNP` repository (`L-meta-060` and `L-meta-066`).

## Checked multiplexer compression

[CompressionTask.lean](PvsNP/CompressionTask.lean) states the task using `Std.Sat.CNF`, Mathlib's `Nat.card` and `Asymptotics.IsLittleO`. The certificate records the source's gate growth, output equality on every input assignment, a bijection from CNF models to accepting source assignments, linear variable and clause bounds, width at most three, and a subexponential exponent after polynomial overhead.

[Multiplexer.lean](PvsNP/Multiplexer.lean) proves the certificate for the multiplexer. Its $n=k+2^k$ input bits comprise $k$ address bits and $2^k$ data bits. The expanded circuit has a separate term for each address and repeats the full address test in each term. Pulling each selector test out of its branch gives a binary tree of multiplexers. Lean checks the exact gate counts

$$
g_{\rm expanded} = 2^{k-1}(3k+2)-1 \quad (k\ge 1),\qquad
g_{\rm factored} = 4(2^k-1).
$$

At $k=4$, there are 20 input bits and the gate count drops from 111 to 60. All emitted gates come from the formulas' expression trees. The encoding uses at most $5n$ declared variables and $13n$ clauses. Lean checks that putting clauses and literals into finite sets preserves exact counts and width, matching the counting theorem's mathematical representation over `Fin v`.

The compressed family can be constructed from $k=\lfloor\log_2 n\rfloor$ under the promise that the source is the specified expanded multiplexer. Visiting the tree, assigning wire indices, constructing the constant-size gate clauses and removing duplicates all have polynomial overhead. Even unary indices give polynomial encoding length. The Mathlib proof transfers the published count bound to $2^{o(n)}$ under that polynomial overhead. The preprocessing estimate is argued at the algorithm level and the Lean certificate covers the count, structural bounds and asymptotic transfer. The multiplexer itself can be counted directly, with $2^{n-1}$ accepting assignments, since each address fixes one data bit and leaves the rest free. It serves as a control family for the compression method. [Published counter and machine-time bound](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/SubexponentialSAT.lean)

```lean
module

import PvsNP.Multiplexer

#check PvsNP.Multiplexer.compression
#print axioms PvsNP.Multiplexer.canonical_model_count
#print axioms PvsNP.Multiplexer.compression
```

### Superlinear Tseitin window and sum-of-products cut compression

[CompressionTask.lean](PvsNP/CompressionTask.lean) also proves the general superlinear `#3-SAT` exponent transfer (`countingScale_isLittleO_of_rpow_log`, `countingScale_isLittleO_of_rpow_log_any`, `logTimeBudget_isLittleO_of_rpow_log_any`, `superlinear_tseitin_isLittleO`): any variable budget $v(n) \le c\,n\,(\log(n+16))^\alpha$ with $\alpha < 1/2$ (whether sublinear, linear, or superlinear such as $n(\log n)^{1/3}$) keeps the counter exponent $o(n)$.

[BranchingCompression.lean](PvsNP/BranchingCompression.lean) generalizes single-CNF compression to additive $2^{o(n)}$-branching certificates (`BranchingCertificate`) and `vp-vnp`-style sum-of-products 3-CNF decompositions (`SumOfProductsCertificate`: $|C^{-1}(1)| = \sum_b \prod_j |\mathrm{Models}(F_{b,j})|$), proves subexponential runtime transfer (`sop_runtime_le_rpow`, `sopLogTimeBudget_isLittleO_of_rpow_log`, `subexponential_of_sopLogTimeBudget`), proves the cut-residual (`branchingOfCutResiduals`) and factored-cut (`sopOfFactoredCut`, `factored_cut_sopLogTimeBudget_isLittleO`) reductions for $o(n)$-wire cuts into $\mathrm{poly}(n)$ factors of $\le c\,n\,(\log n)^\alpha$ variables ($\alpha < 1/2$), and checks an explicit $\Theta(n^2)$-gate circuit family (`QuadraticHubPods.source`, `source_quadratic_gates`) whose 1-wire hub cut yields a 2-branch, $(k+1)$-factor sum-of-products 3-CNF certificate with at most 4 variables per factor and $o(n)$ log-time budget (`QuadraticHubPods.sopCertificate`, `sopCertificate_var_bound`, `sopCertificate_subexponential`).

[LiteralPropagation.lean](PvsNP/LiteralPropagation.lean) formalizes zero-variable `.not` / alias / constant / idempotence / complementary symbolic literal propagation (`compileSym`, `compiledCNF`, `compiledModelsEquiv`, `prunedModelsEquiv`, `pruned_vars_le`) together with cut-based reader elimination (`branchingOfPinnedCut`, `unhitBinaryGates_pinOfCut`, `branchingOfPinnedCut_vars_le`, `hitting_cut_subexponential`), showing that pinning an $o(n)$-size cut hitting all but $O(n(\log n)^\alpha)$ ($\alpha < 1/2$) binary `AND`/`OR` gates runs in $2^{o(n)}$ deterministic exact `#SAT` time.

[BlockContraction.lean](PvsNP/BlockContraction.lean) formalizes deterministic DAG block contraction (`BlockCircuit`), overcoming the bounded-fanout hitting-cut obstruction via exact truth-table compilation (`acceptingAssignmentsEquiv`, `encode_size` $= B \cdot 2^d + 1$, `encode_width` $\le d + 1$ over $n + B$ variables), subexponential `#SAT` transfer (`BlockContractionCertificate`, `block_contraction_subexponential` for $O(n(\log n)^\alpha)$ blocks with $\alpha < 1/2$, plus `depth_contraction_ratio_ge`), the universal bounded-fanout hitting-cut obstruction (`binaryGateCount_le_unhit_add_sum_fanout`, `binaryGateCount_le_unhit_add_maxFanout`), and the concrete $\Theta(n^2)$-gate max-fanout-`2` separation witness `DenseChainBlocks` (`source_quadratic_binaryGates`, `source_fanout_le_two`, `source_hitting_cut_lower`, `DenseChainBlocks.subexponential` using $2k + 1$ blocks and $\le 2n$ variables).

[StrideContraction.lean](PvsNP/StrideContraction.lean) builds an automatic general-circuit compiler (`compileStride`, `strideCertificate`) that contracts **any** fan-in-2 circuit at stride $h \ge 1$ into a $2^h$-input `BlockCircuit` by phase-averaging over $r \in \mathrm{Fin}\,h$ (`exists_stride_residue_le`), yielding at most $\lfloor \mathrm{totalTruncatedSpan}(c,h) / h \rfloor + 1$ blocks (`strideCertificate_blocks_le`; at most $\lfloor c.\mathrm{gateCount}/h \rfloor + 1$ for unit-span layered circuits via `totalTruncatedSpan_layered_le`, `strideCertificate_layered_blocks_le`), combines $o(n)$ wire cuts with automatic stride-$h$ residual contraction (`HybridBlockCertificate`, `hybridOfCutStride`, `hybrid_block_subexponential`), and instantiates an automatic factor-$h$ reduction on synchronous cyclic ring circuits (`LayeredRing.source_gateCount`, `LayeredRing.source_unit_span`, `LayeredRing.automatic_stride_contraction`, `LayeredRing.subexponential`).

[ValiantReduction.lean](PvsNP/ValiantReduction.lean) extends the pipeline with Valiant's bit-level depth-reduction lemma (`exists_subset_sum_le`, `residualDepth`, `valiantDepthReduction`, `valiant_halving_cut`: on any circuit of binary depth $< 2^k$, cutting $\le 2t\cdot \mathrm{binaryGateCount}/k$ wires forces all residual cone depths $< 2^{k-t}$), a universal residual-depth compiler (`compileResidualDepth`, `depthCutCertificate`, `valiantBlockCertificate`, `depthCut_subexponential` reducing to `BlockContractionCertificate source (2^H)`), and the sharp $O(n \log n)$ bounded-fanout skip-wire barrier `SkipRing` (`source_binaryGateCount`, `source_fanout_le_three`, `source_hitting_cut_lower`, `source_totalTruncatedSpan_ge`, `source_crossingWires_ge`, `source_strideCertificate_blocks_ge`, `source_escapes_stride_subexponential_window`, `source_valiant_span_invariant`): at logarithmic depth $D = \lfloor\log_2 n\rfloor + s$, `SkipRing` has $O(n\log n)$ gates and fanout $\le 3$ (blocking `LiteralPropagation`), escapes `StrideContraction`'s $O(n(\log n)^\alpha)$ ($\alpha < 1$) block window, while Valiant's depth cut ignores `wireSpan` completely—showing formally why constant-width truth-table CNF contraction hits a wall at $O(n \log n)$ and non-CNF circuit-CSP constraints are needed beyond it.

[CircuitCSP.lean](PvsNP/CircuitCSP.lean) replaces truth-table CNF expansion with exact-counting non-CNF local circuit constraints (`LocalCircuitConstraint`, `CircuitCSP`, `CircuitCSPCertificate`, `embedSub`, `compileCircuitCSP`, `depthCutCSPCertificate`, `valiantCSPCertificate`), proves exponential representation savings per block (`csp_vs_cnf_per_block_gap`, `csp_vs_cnf_depth_gap`: $2^H + 2 < 2^{2^H}$ for $H \ge 2$), establishes the exact shallow-vs-deep $O(n \log n)$ Valiant phase diagram (`valiant_deep_nlogn_subexponential` when depth-bitwidth $k(n) \ge c_k (\log n)^\gamma$, $\gamma > 1/2$, vs `valiant_shallow_nlogn_wall` and `SkipRing.source_escapes_valiant_shallow_wall` when $k(n) = O(\log\log n)$), and constructs the concrete deep $O(n\log n)$ skip-chain separation witness `DeepSkipChain` (`source_escapes_stride_subexponential_window` vs `source_valiant_linear_vars` and `DeepSkipChain.valiant_subexponential`).

[CircuitCSPTradeoff.lean](PvsNP/CircuitCSPTradeoff.lean) closes the end-to-end incidence/arity gap (`CircuitCSP.maxArity`, `CircuitCSP.maxBinaryGates`, `cspIncidenceBudget_isLittleO_of_rpow_log`, `cspArityBudget_isLittleO_of_rpow_log`), proves the sharp $\sqrt{\log n}$ threshold (`countingScale_not_isLittleO_of_sqrt_log`, `cspIncidenceBudget_not_isLittleO_of_sqrt_log`) and the universal Valiant arity-vs-cut-size wall (`nat_div_valiant_ge_residual`, `valiant_universal_arity_cut_wall`, `valiant_quasipoly_arity_wall`, `valiant_poly_arity_wall`: across **all** depths, keeping worst-case Valiant constraint arity $2^{2^{k-t}} \le \mathrm{poly}(n)$ forces $k - t = O(\log\log n)$ and pushes Valiant cut size outside $O(n(\log n)^\alpha)$ for all $\alpha < 1$), builds the DAG-preserving slice compiler (`extractSubDAG`, `SliceCSPState`, `dagSliceCSPCertificate`), and breaks that generic Valiant wall on `DeepSkipChain` via periodic width-$s$ cuts (`DeepSkipChain.sliceCertificate`, `DeepSkipChain.sliceCertificate_end_to_end_subexponential`).

[SeparatorBarrier.lean](PvsNP/SeparatorBarrier.lean) separates the shallow $O(\log n)$-depth $O(n\log n)$-gate frontier by balanced vertex separators: proves that `SkipRing` collapses into $2^{o(n)}$ exact `#3-SAT` time via balanced column separators (`podCircuit`, `podCircuit_factored_iff`, `SkipRing.separatorSOPCertificate`, `SkipRing.separatorSOPCertificate_vars_le`, `SkipRing.separator_subexponential` at block width $p = \Theta(\log^2 n)$), constructs the explicit $O(\log n)$-depth, $O(n\log n)$-gate, max-fanout-$\le 2$ butterfly family `ButterflyNet.source` defeating `LiteralPropagation`, `StrideContraction`, and all Valiant cut schedules (`source_binaryGateCount`, `source_wireDepth`, `source_fanout_le_two`, `source_hitting_cut_lower`, `source_stride_blocks_ge`, `source_escapes_stride_subexponential_window`, `source_escapes_valiant_shallow_wall`), and establishes an $\Omega(n)$ balanced vertex separator lower bound (`CircuitEdge`, `UndirectedReachAvoiding`, `SeparatesInputs`, `bfly_walk_hits_separator`, `bfly_vertex_congestion_le`, `butterfly_separator_lower_bound`, `butterfly_balanced_separator_linear`, `butterfly_component_separator_linear`, `butterfly_escapes_sublinear_separator`: every balanced separator requires $|S| \ge n / 18$).

[AffineButterflyBarrier.lean](PvsNP/AffineButterflyBarrier.lean) sharpens and breaks the `ButterflyNet` barrier along both topological and semantic axes: lifts the $\Omega(n)$ separator bound to arbitrary-degree tree decompositions (`DecompTree`, `TreeDecomp`, `butterfly_treewidth_linear`: $2^d \le 18\,(\mathrm{width}+1)$, `butterfly_escapes_sublinear_treewidth`) and binary tensor-contraction trees (`ContractionTree`, `ValidContractionTree`, `butterfly_contractionWidth_linear`, `butterfly_gateContractionWidth_linear`: $2^d \le 18\,\mathrm{contractionWidth}$, `butterfly_escapes_sublinear_contractionWidth`), formalizes `HybridCircuit` (`AND`/`OR`/`XOR`/`NOT`), exact $\mathbb{F}_2$ affine subspace counting (`linearSystem_card_eq_zero_or_pow`), and the universal $3^q$-branch affine decomposition (`acceptCount_eq_sum_affine`, `affineBranchLogTimeBudget_isLittleO` giving $2^{o(n)}$ whenever nonlinear gate count $q = o(n)$), and proves an explicit exponential separation on `HybridButterflyNet.source d q`—matching `ButterflyNet`'s $\Omega(n)$ treewidth and contraction width for all $q$ (`hybridBfly_edge_iff`, `hybridBfly_treewidth_linear`, `hybridBfly_gateContractionWidth_linear`) while collapsing to exact count $2^{2^d-1}$ at $q=0$ (`xorBfly_acceptCount`) and $2^{o(n)}$ for all $q = o(n)$ (`hybridBfly_subexponential_of_sublinear_nonlinear`), vs. $\Theta(n\log n)$ nonlinear gates (`butterfly_allNonlinear_escapes_sublinear_budget`). [ReachableSemanticBarrier.lean](PvsNP/ReachableSemanticBarrier.lean) exposes the single-output reachable-wire loophole of `ButterflyNet.source` (`2 * 2^d - 1` reachable wires, linear compression `source_linear_compression`, and closed-form count `bflyTreeCount`), proves subgraph monotonicity for treewidth and gate contraction width (`TreeDecomp.restrict_le`, `ValidContractionTree.restrict_le`), and constructs `ClosedComparatorXor.source d` with `(d + 2) * 2^d - 1` wires: every wire reaches the output (`all_wires_reachable`), all `(d + 1) * 2^d` comparator-butterfly wires compute pairwise distinct Boolean functions (`bfly_wires_pairwise_distinct`), treewidth/contraction width/nonlinear count defeat all `o(2^d)` bounds (`escapes_sublinear_treewidth`, `escapes_sublinear_contractionWidth`, `escapes_sublinear_nonlinear`), and `ℤ/2ℤ` parity conservation yields `2 ^ (2 ^ d - 1)` accepting assignments (`layer_xor_invariant`, `acceptCount_eq`). [AlgebraicDegreeBarrier.lean](PvsNP/AlgebraicDegreeBarrier.lean) formalizes exact `ℤ/2ℤ` ANF Möbius inversion (`anf_eval`, `anfDegree`), proving `anfDegree (ClosedComparatorXor.source d).eval = 1` vs `anfDegree (allAnd n) = n`, proves exact integer Hamming-weight conservation across every comparator butterfly layer (`ClosedComparatorXor.layer_hammingWeight_invariant`, `layer_allTrue_iff`), and constructs the purely nonlinear (`AND`/`OR` only, `(d + 1) * 2^d - 1` nonlinear gates) `ClosedComparatorAnd.source d` with 100% reachability, 100% pairwise wire distinctness, `Ω(2^d)` treewidth & contraction width, maximal ANF degree `2^d` (`output_anfDegree_eq`), and exact `#Circuit-SAT` collapse `1` (`acceptCount_eq`).

Check the full `PvsNP` library with warnings as errors:

```sh
lake build --wfail PvsNP
```

## ETH reproduction projects on the server

Each checkout under `~/Documents/math/eth-sources` uses its own pinned `lean-toolchain` and Lake manifest.

| Directory | Source revision | Build targets |
| --- | --- | --- |
| `anthropic/eth` | [16a5ce4](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth) | `lake build Solution`, then `lake env lean scripts/PrintAxioms.lean` |
| `openai/lean` | [4eaee87](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean) | `lake build OAI.Algorithms.SubexponentialSAT.Main` |
| `complexitylib` | [6a5fb39](https://github.com/cslib-community/cslib-frontier/tree/6a5fb39b1da33ce1f41adf0f9b234982e48e33ef) | `lake build ComplexityAbstracts.CookLevinBridge ComplexityAbstracts.SubexponentialSATBridge Complexity.Computability.Complexity.FineGrained.CircuitCounting` |

The first two checkouts use `lake exe cache get` for Mathlib. The frontier checkout uses `scripts/cache/ensure.sh` for its Mathlib and library caches. Its circuit counting target is the most direct starting point for machine-level extensions of the local semantic model. The OpenAI source build logs to `openai/lean/eth-build.log` under the checkout root above.
