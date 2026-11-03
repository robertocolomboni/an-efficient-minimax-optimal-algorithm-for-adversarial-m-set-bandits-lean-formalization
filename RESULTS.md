# Correspondence with the manuscript

Links refer to the included [PDF](paper/main.pdf) and Lean source files.

| Paper result | Lean declaration |
| --- | --- |
| [Informal upper bound, Section 3.1 (p. 5)](paper/main.pdf#page=5) | [`MsetsPaper.Alignment.efficiency_and_regret_ambient`](MsetsPaper/Alignment/ReleaseIntroduction.lean) |
| [Informal lower bound, Section 3.2 (p. 7)](paper/main.pdf#page=7) | [`MsetsPaper.Alignment.LowerDefinitive.theorem_lower_bound`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Theorem 1 (p. 12)](paper/main.pdf#page=12) | [`MsetsPaper.Alignment.upper_main_regret_ambient_of_conditional_expectations`](MsetsPaper/Alignment/UpperAmbient.lean) |
| [Theorem 2 (p. 15)](paper/main.pdf#page=15) | [`MsetsPaper.Alignment.LowerDefinitive.theorem_lower_bound`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Theorem 3 (p. 40)](paper/main.pdf#page=40) | [`MsetsPaper.Alignment.LowerDefinitive.theorem_lower_bound_explicit`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Corollary 1 (p. 20)](paper/main.pdf#page=20) | [`MsetsPaper.Alignment.OrdinaryDefinitive.corollary_ordinary_bandits`](MsetsPaper/Alignment/OrdinaryDefinitive.lean) |
| [Lemma 1 (p. 11)](paper/main.pdf#page=11) | [`MsetsPaper.Alignment.upper_linear_majorant`](MsetsPaper/Alignment/UpperStructural.lean) |
| [Lemma 2 (p. 24)](paper/main.pdf#page=24) | [`MsetsPaper.Alignment.upper_inverse_covariance_identity`](MsetsPaper/Alignment/UpperStructural.lean) |
| [Lemma 3 (p. 26)](paper/main.pdf#page=26) | [`MsetsPaper.Alignment.upper_bounded_increments`](MsetsPaper/Alignment/UpperStructural.lean) |
| [Lemma 4 (p. 26)](paper/main.pdf#page=26) | [`MsetsPaper.Alignment.upper_omd_stability_ambient_uniform`](MsetsPaper/Alignment/UpperAmbientOMDUniform.lean) |
| [Lemma 5 (p. 27)](paper/main.pdf#page=27) | [`MsetsPaper.Alignment.upper_kw_concentration_ambient`](MsetsPaper/Alignment/UpperAmbientConcentration.lean) |
| [Lemma 6 (p. 30)](paper/main.pdf#page=30) | [`MsetsPaper.Alignment.upper_leverage_concentration_ambient`](MsetsPaper/Alignment/UpperAmbientL6.lean) |
| [Lemma 7 (p. 34)](paper/main.pdf#page=34) | [`MsetsPaper.Alignment.Implementation.projection_dual_paper`](MsetsPaper/Alignment/ImplementationOfficial.lean) |
| [Lemma 8 (p. 35)](paper/main.pdf#page=35) | [`MsetsPaper.Alignment.approximate_projection_extendedKL`](MsetsPaper/Alignment/ExtendedKL.lean) |
| [Lemma 9 (p. 38)](paper/main.pdf#page=38) | [`MsetsPaper.Alignment.Implementation.esp_routines`](MsetsPaper/Alignment/ImplementationESP.lean) |
| [Lemma 10 (p. 41)](paper/main.pdf#page=41) | [`MsetsPaper.Alignment.LowerDefinitive.lemma_lower_fixing_table`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Lemma 11 (p. 41)](paper/main.pdf#page=41) | [`MsetsPaper.Alignment.LowerDefinitive.lemma_lower_complement`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Lemma 12 (p. 42)](paper/main.pdf#page=42) | [`MsetsPaper.Alignment.LowerDefinitive.lemma_lower_feedback_density`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Lemma 13 (p. 43)](paper/main.pdf#page=43) | [`MsetsPaper.Alignment.LowerDefinitive.lemma_lower_mean_to_probability`](MsetsPaper/Alignment/LowerDefinitive.lean) |
| [Proposition 1 (p. 14)](paper/main.pdf#page=14) | [`MsetsPaper.Alignment.Implementation.efficient_implementation_with_subcosts`](MsetsPaper/Alignment/ImplementationCosts.lean) |
| [Proposition 2 (p. 43)](paper/main.pdf#page=43) | [`MsetsPaper.Lower.SparseCapped.lower_action_count_sparse_action_losses`](MsetsPaper/Lower/SparseCappedConclusion.lean) |
| [Proposition 3 (p. 48)](paper/main.pdf#page=48) | [`MsetsPaper.Lower.DenseCommonNoise.lower_action_count_dense_action_losses`](MsetsPaper/Lower/DenseCommonNoiseConclusion.lean) |
| [Proposition 4 (p. 51)](paper/main.pdf#page=51) | [`MsetsPaper.Lower.ConfidenceOblivious.lower_confidence_oblivious_action_losses`](MsetsPaper/Lower/ConfidenceObliviousConclusion.lean) |
| [Minimax synthesis, Section 1 (p. 2)](paper/main.pdf#page=2) | [`MsetsPaper.Alignment.matching_high_probability_rates`](MsetsPaper/Alignment/Synthesis.lean) |
| [Introductory W,J construction, Section 3.2 (pp. 7–9)](paper/main.pdf#page=7) | [`MsetsPaper.Lower.WJ.introductory_lower_bound_private_seed`](MsetsPaper/Lower/WJConclusion.lean) |

Lower-bound interfaces for persistent private learner randomness are in
[`PrivateSeedEndpoints.lean`](MsetsPaper/Lower/PrivateSeedEndpoints.lean) and the corresponding alignment modules.

The W,J endpoint uses the sketch's integer assumptions, with `k ≥ 255`,
`d = 32k`, `cd = 4T`, and `T ≥ d log d`; its probability is at least `1/8`
at threshold `2⁻¹⁴ √(dT log d)`.
It applies event data processing before finite-mixture convexity and fixes
the favorable set before fixing the noise.
The projection proof represents the KKT multipliers by their positive and negative parts.
See the README for the computational model and scope of the verification.
