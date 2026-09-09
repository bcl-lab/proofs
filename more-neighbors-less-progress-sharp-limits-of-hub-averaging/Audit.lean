import HubAveraging
import CutAndBudget
import Network
import GraphMoments
import RandomSweep
import PermutationMean
import EdgeProcess
import GraphCut
import SpectralBridge
import GraphSpectral
import UniformPolicy
import Minimax
import RandomCut
import SpectrumEndpoints
import EqualBudget
import GapRange
import Asymptotic

#print axioms HubAveraging.pair_energy_loss
#print axioms HubAveraging.pair_preserves_sum
#print axioms HubAveraging.sweep_preserves_sum
#print axioms HubAveraging.sweep_energy_loss
#print axioms HubAveraging.equal_leaf_sweep_loss
#print axioms HubAveraging.bipartition_witness_loss
#print axioms HubAveraging.reversed_bipartition_witness_loss
#print axioms HubAveraging.common_witness_expectation
#print axioms HubAveraging.expectation_lower_bound
#print axioms HubAveraging.policy_witness_ratio
#print axioms HubAveraging.r_nonneg
#print axioms HubAveraging.weighted_r_lt_one
#print axioms HubAveraging.coefficient_bounds
#print axioms HubAveraging.gamma_pos
#print axioms HubAveraging.spectral_factorization
#print axioms HubAveraging.bipartition_spectral_value
#print axioms HubAveraging.threshold_identity
#print axioms HubAveraging.spectral_threshold
#print axioms HubAveraging.spectral_energy_bound
#print axioms HubAveraging.beta_from_physical_sweep
#print axioms HubAveraging.unit_hub_column_norm
#print axioms HubAveraging.coefficient_trace_identity
#print axioms HubAveraging.degree_three_values
#print axioms HubAveraging.threshold_le_degree
#print axioms HubAveraging.all_opposite_orders_loss
#print axioms HubAveraging.all_selectors_expected_loss
#print axioms HubAveraging.block_energy_floor
#print axioms HubAveraging.sum_preserving_block_bound
#print axioms HubAveraging.two_sign_variance
#print axioms HubAveraging.supported_energy_loss
#print axioms HubAveraging.concrete_cut_loss_bound
#print axioms HubAveraging.closed_neighborhood_cut_constant
#print axioms HubAveraging.cut_constant_le
#print axioms HubAveraging.cut_residual_ratio
#print axioms HubAveraging.local_solve_fraction
#print axioms HubAveraging.loss_polynomial_from_moments
#print axioms HubAveraging.concave_quadratic_endpoint
#print axioms HubAveraging.independent_budget_exponential
#print axioms HubAveraging.exponential_chord
#print axioms HubAveraging.benchmark_500_exact
#print axioms HubAveraging.separation_ratio_bound
#print axioms HubAveraging.hub_progress_500_upper
#print axioms HubAveraging.benchmark_500_real
#print axioms HubAveraging.benchmark_500_combined
#print axioms HubAveraging.disagreement_nonneg
#print axioms HubAveraging.disagreement_of_total_zero
#print axioms HubAveraging.pairUpdate_off
#print axioms HubAveraging.pairUpdate_energy
#print axioms HubAveraging.pairUpdate_total
#print axioms HubAveraging.networkSweep_total
#print axioms HubAveraging.networkSweep_energy
#print axioms HubAveraging.actionOrder_nodup
#print axioms HubAveraging.actionOrder_mem
#print axioms HubAveraging.actionOrder_length
#print axioms HubAveraging.regular_neighbor_sum
#print axioms HubAveraging.regular_bipartition_total_zero
#print axioms HubAveraging.sign_energy
#print axioms HubAveraging.graph_witness_residual
#print axioms HubAveraging.centered_energy_expansion
#print axioms HubAveraging.disagreement_expansion
#print axioms HubAveraging.disagreement_loss
#print axioms HubAveraging.sweepLoss_nonneg
#print axioms HubAveraging.action_disagreement_le
#print axioms HubAveraging.policyRatio_le_one
#print axioms HubAveraging.ratio_le_worstResidual
#print axioms HubAveraging.policy_witness_exact
#print axioms HubAveraging.signState_values
#print axioms HubAveraging.signState_opposite
#print axioms HubAveraging.bipartite_policy_lower_bound
#print axioms HubAveraging.bipartite_minimax_lower_bound
#print axioms HubAveraging.finset_centered_expansion
#print axioms HubAveraging.localS_expansion
#print axioms HubAveraging.localH_expansion
#print axioms HubAveraging.lapQuadratic_expansion
#print axioms HubAveraging.lap_energy_expansion
#print axioms HubAveraging.graph_S_moment
#print axioms HubAveraging.graph_H_moment
#print axioms HubAveraging.graph_loss_polynomial
#print axioms HubAveraging.localFormula_recurrence_coefficients
#print axioms HubAveraging.localFormula_average
#print axioms HubAveraging.randomSweepLoss_formula
#print axioms HubAveraging.perm_tail_sum
#print axioms HubAveraging.permutationLoss_step
#print axioms HubAveraging.uniform_permutation_loss
#print axioms HubAveraging.pair_disagreement_loss
#print axioms HubAveraging.directed_difference_sum
#print axioms HubAveraging.edgeAverage_disagreement
#print axioms HubAveraging.edgeAverage_mono
#print axioms HubAveraging.edgeAverage_scale
#print axioms HubAveraging.independent_edge_contraction
#print axioms HubAveraging.sign_relative
#print axioms HubAveraging.sign_block_sum
#print axioms HubAveraging.closedBlock_card
#print axioms HubAveraging.closedBlock_same_card
#print axioms HubAveraging.sign_closedBlock_sum_sq
#print axioms HubAveraging.sign_closedBlock_energy
#print axioms HubAveraging.graph_cut_energy_cap
#print axioms HubAveraging.supported_total
#print axioms HubAveraging.graph_cut_residual
#print axioms HubAveraging.energy_dot
#print axioms HubAveraging.orthogonal_dot
#print axioms HubAveraging.hermitian_polynomial_expansion
#print axioms HubAveraging.hermitian_threshold_bound
#print axioms HubAveraging.laplacian_matrix
#print axioms HubAveraging.lapQuadratic_upper
#print axioms HubAveraging.lap_eigenvalue_upper
#print axioms HubAveraging.centered_zero_eigen_coordinates
#print axioms HubAveraging.centered_graph_threshold
#print axioms HubAveraging.localFormula_b
#print axioms HubAveraging.uniform_permutation_SH
#print axioms HubAveraging.hubMeanLoss_permutation
#print axioms HubAveraging.hubMeanLoss_local_identity
#print axioms HubAveraging.action_count_regular
#print axioms HubAveraging.uniform_policy_loss
#print axioms HubAveraging.uniform_graph_operator
#print axioms HubAveraging.centeredState_total
#print axioms HubAveraging.centeredState_energy
#print axioms HubAveraging.laplacian_centeredState
#print axioms HubAveraging.laplacian_total
#print axioms HubAveraging.lapQuadratic_centeredState
#print axioms HubAveraging.graph_threshold_all
#print axioms HubAveraging.action_energy_disagreement_loss
#print axioms HubAveraging.uniform_expected_residual
#print axioms HubAveraging.uniform_ratio_upper
#print axioms HubAveraging.exact_bipartite_minimax
#print axioms HubAveraging.cutCap_le_maximum
#print axioms HubAveraging.cutMaximum_le
#print axioms HubAveraging.arbitrary_random_cut_bound
#print axioms HubAveraging.lap_eigenvector_energy
#print axioms HubAveraging.lap_eigenvector_centered
#print axioms HubAveraging.lap_eigenvector_moments
#print axioms HubAveraging.uniform_eigenvector_ratio
#print axioms HubAveraging.graph_interval_bound
#print axioms HubAveraging.uniform_endpoint_formula
#print axioms HubAveraging.exists_nonzero_lap_eigenvalue
#print axioms HubAveraging.exists_uniform_spectral_endpoints
#print axioms HubAveraging.graph_poincare
#print axioms HubAveraging.edgeResidual_nonneg
#print axioms HubAveraging.edgeWorst_bound
#print axioms HubAveraging.edge_budget_exponential
#print axioms HubAveraging.bipartite_witness_disagreement
#print axioms HubAveraging.equal_budget_separation
#print axioms HubAveraging.contrast_total
#print axioms HubAveraging.contrast_energy
#print axioms HubAveraging.contrast_neighbor_zero
#print axioms HubAveraging.contrast_quadratic
#print axioms HubAveraging.bipartite_gap_le_degree
#print axioms HubAveraging.bipartite_degree_half
#print axioms HubAveraging.bipartite_gap_half
#print axioms HubAveraging.equal_budget_separation_graph
#print axioms HubAveraging.pairUpdate_symmetric
#print axioms HubAveraging.progress_ratio_nonneg
#print axioms HubAveraging.vanishing_separation
