use std::collections::BTreeMap;

use anyhow::{anyhow, bail, Context, Result};
use chrono::Utc;
use nalgebra::{DMatrix, DVector};
use serde::{Deserialize, Serialize};

pub const CANDIDATE_FEATURES: &[&str] = &[
    "sha_calls",
    "sha_bytes",
    "merkle_levels",
    "proof_bytes",
    "upload_bytes",
    "upload_chunks",
    "heap_pages_32k",
    "ro_account_count",
    "rw_account_count",
    "account_data_bytes_read",
    "account_data_bytes_written",
    "field_add_sub_ops",
    "field_mul_ops",
    "field_inv_ops",
    "extension_mul_ops",
];

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SvmLimits {
    pub max_compute_units_per_tx: u64,
    pub max_transaction_bytes: u64,
    pub max_heap_frame_bytes: u64,
    pub stack_frame_bytes: u64,
}

impl Default for SvmLimits {
    fn default() -> Self {
        Self {
            max_compute_units_per_tx: 1_400_000,
            max_transaction_bytes: 1_232,
            max_heap_frame_bytes: 262_144,
            stack_frame_bytes: 4_096,
        }
    }
}

impl SvmLimits {
    pub fn heap_pages_32k(&self, heap_frame_bytes: u64) -> u64 {
        heap_frame_bytes.div_ceil(32 * 1024)
    }

    pub fn compute_headroom(&self, predicted_cu: f64) -> f64 {
        self.max_compute_units_per_tx as f64 - predicted_cu
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FeatureOrigin {
    DirectMeasurement,
    DerivedStructure,
    EstimatedProxy,
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MeasurementStatus {
    Success,
    Failed,
    Skipped,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BenchmarkKind {
    Noop,
    HashSyscall,
    MerklePath,
    ProofParsing,
    FieldArithmetic,
    HeapFrame,
    AccountIo,
    UploadPath,
    SyntheticVerifier,
    FailureBoundary,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CostFeatures {
    pub sha_calls: u64,
    pub sha_bytes: u64,
    pub merkle_paths: u64,
    pub merkle_levels: u64,
    pub proof_bytes: u64,
    pub proof_segments: u64,
    pub upload_bytes: u64,
    pub upload_chunks: u64,
    pub heap_frame_bytes_requested: u64,
    pub heap_pages_32k: u64,
    pub ro_account_count: u64,
    pub rw_account_count: u64,
    pub account_data_bytes_read: u64,
    pub account_data_bytes_written: u64,
    pub field_add_sub_ops: u64,
    pub field_mul_ops: u64,
    pub field_inv_ops: u64,
    pub extension_mul_ops: u64,
}

impl CostFeatures {
    pub fn get(&self, name: &str) -> Result<f64> {
        let value = match name {
            "sha_calls" => self.sha_calls as f64,
            "sha_bytes" => self.sha_bytes as f64,
            "merkle_levels" => self.merkle_levels as f64,
            "proof_bytes" => self.proof_bytes as f64,
            "upload_bytes" => self.upload_bytes as f64,
            "upload_chunks" => self.upload_chunks as f64,
            "heap_pages_32k" => self.heap_pages_32k as f64,
            "ro_account_count" => self.ro_account_count as f64,
            "rw_account_count" => self.rw_account_count as f64,
            "account_data_bytes_read" => self.account_data_bytes_read as f64,
            "account_data_bytes_written" => self.account_data_bytes_written as f64,
            "field_add_sub_ops" => self.field_add_sub_ops as f64,
            "field_mul_ops" => self.field_mul_ops as f64,
            "field_inv_ops" => self.field_inv_ops as f64,
            "extension_mul_ops" => self.extension_mul_ops as f64,
            other => bail!("unknown feature: {other}"),
        };
        Ok(value)
    }

    pub fn named_values(&self) -> Vec<(&'static str, f64)> {
        CANDIDATE_FEATURES
            .iter()
            .map(|name| (*name, self.get(name).unwrap_or_default()))
            .collect()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MeasurementRecord {
    pub measurement_id: String,
    pub benchmark: BenchmarkKind,
    pub label: String,
    pub repetition: u32,
    pub timestamp_utc: String,
    pub svm_limits: SvmLimits,
    pub features: CostFeatures,
    pub feature_origins: BTreeMap<String, FeatureOrigin>,
    pub actual_cu: Option<u64>,
    pub transaction_bytes: Option<u64>,
    pub status: MeasurementStatus,
    pub error: Option<String>,
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CoefficientEstimate {
    pub estimate: f64,
    pub stderr: Option<f64>,
    pub rationale: String,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CostCoefficients {
    pub intercept: Option<CoefficientEstimate>,
    pub sha_calls: Option<CoefficientEstimate>,
    pub sha_bytes: Option<CoefficientEstimate>,
    pub merkle_levels: Option<CoefficientEstimate>,
    pub proof_bytes: Option<CoefficientEstimate>,
    pub upload_bytes: Option<CoefficientEstimate>,
    pub upload_chunks: Option<CoefficientEstimate>,
    pub heap_pages_32k: Option<CoefficientEstimate>,
    pub ro_account_count: Option<CoefficientEstimate>,
    pub rw_account_count: Option<CoefficientEstimate>,
    pub account_data_bytes_read: Option<CoefficientEstimate>,
    pub account_data_bytes_written: Option<CoefficientEstimate>,
    pub field_add_sub_ops: Option<CoefficientEstimate>,
    pub field_mul_ops: Option<CoefficientEstimate>,
    pub field_inv_ops: Option<CoefficientEstimate>,
    pub extension_mul_ops: Option<CoefficientEstimate>,
}

impl CostCoefficients {
    pub fn set(&mut self, name: &str, value: CoefficientEstimate) -> Result<()> {
        match name {
            "intercept" => self.intercept = Some(value),
            "sha_calls" => self.sha_calls = Some(value),
            "sha_bytes" => self.sha_bytes = Some(value),
            "merkle_levels" => self.merkle_levels = Some(value),
            "proof_bytes" => self.proof_bytes = Some(value),
            "upload_bytes" => self.upload_bytes = Some(value),
            "upload_chunks" => self.upload_chunks = Some(value),
            "heap_pages_32k" => self.heap_pages_32k = Some(value),
            "ro_account_count" => self.ro_account_count = Some(value),
            "rw_account_count" => self.rw_account_count = Some(value),
            "account_data_bytes_read" => self.account_data_bytes_read = Some(value),
            "account_data_bytes_written" => self.account_data_bytes_written = Some(value),
            "field_add_sub_ops" => self.field_add_sub_ops = Some(value),
            "field_mul_ops" => self.field_mul_ops = Some(value),
            "field_inv_ops" => self.field_inv_ops = Some(value),
            "extension_mul_ops" => self.extension_mul_ops = Some(value),
            other => bail!("unknown coefficient: {other}"),
        }
        Ok(())
    }

    pub fn get(&self, name: &str) -> Option<&CoefficientEstimate> {
        match name {
            "intercept" => self.intercept.as_ref(),
            "sha_calls" => self.sha_calls.as_ref(),
            "sha_bytes" => self.sha_bytes.as_ref(),
            "merkle_levels" => self.merkle_levels.as_ref(),
            "proof_bytes" => self.proof_bytes.as_ref(),
            "upload_bytes" => self.upload_bytes.as_ref(),
            "upload_chunks" => self.upload_chunks.as_ref(),
            "heap_pages_32k" => self.heap_pages_32k.as_ref(),
            "ro_account_count" => self.ro_account_count.as_ref(),
            "rw_account_count" => self.rw_account_count.as_ref(),
            "account_data_bytes_read" => self.account_data_bytes_read.as_ref(),
            "account_data_bytes_written" => self.account_data_bytes_written.as_ref(),
            "field_add_sub_ops" => self.field_add_sub_ops.as_ref(),
            "field_mul_ops" => self.field_mul_ops.as_ref(),
            "field_inv_ops" => self.field_inv_ops.as_ref(),
            "extension_mul_ops" => self.extension_mul_ops.as_ref(),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelMetrics {
    pub record_count: usize,
    pub rmse: f64,
    pub mae: f64,
    pub p95_abs_error: f64,
    pub max_abs_error: f64,
    pub r_squared: Option<f64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FittedCostModel {
    pub method: String,
    pub selected_features: Vec<String>,
    pub dropped_features: Vec<String>,
    pub coefficients: CostCoefficients,
    pub metrics: ModelMetrics,
    pub uncertainty_rmse: f64,
    pub condition_number: Option<f64>,
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelComparison {
    pub chosen: FittedCostModel,
    pub ols: FittedCostModel,
    pub huber: FittedCostModel,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TransportCostFeatures {
    pub sha_calls: u64,
    pub sha_bytes: u64,
    pub upload_bytes: u64,
    pub upload_chunks: u64,
}

impl TransportCostFeatures {
    pub fn as_cost_features(&self) -> CostFeatures {
        CostFeatures {
            sha_calls: self.sha_calls,
            sha_bytes: self.sha_bytes,
            upload_bytes: self.upload_bytes,
            upload_chunks: self.upload_chunks,
            ..CostFeatures::default()
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileParameterChoice {
    pub name: String,
    pub value: String,
    pub rationale: String,
    #[serde(default)]
    pub sources: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "model", rename_all = "snake_case")]
pub enum QuerySoundnessModel {
    Fri {
        query_count: u64,
        log_blowup: u32,
        #[serde(default)]
        query_proof_of_work_bits: u32,
        target_bits: f64,
        #[serde(default)]
        sources: Vec<String>,
        #[serde(default)]
        notes: Vec<String>,
    },
    Whir {
        query_count: u64,
        log_inv_rate: u32,
        #[serde(default)]
        pow_bits: u32,
        target_bits: f64,
        #[serde(default)]
        sources: Vec<String>,
        #[serde(default)]
        notes: Vec<String>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuerySoundnessAssessment {
    pub model: String,
    pub query_count: u64,
    pub target_bits: f64,
    pub lower_bits: f64,
    pub lower_assumption: String,
    #[serde(default)]
    pub upper_bits: Option<f64>,
    #[serde(default)]
    pub upper_assumption: Option<String>,
    pub meets_target: bool,
    #[serde(default)]
    pub notes: Vec<String>,
    #[serde(default)]
    pub sources: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileScoreInput {
    pub name: String,
    pub features: CostFeatures,
    #[serde(default)]
    pub protocol_family: Option<String>,
    #[serde(default)]
    pub transport: TransportCostFeatures,
    #[serde(default)]
    pub parameter_choices: Vec<ProfileParameterChoice>,
    #[serde(default)]
    pub references: Vec<String>,
    #[serde(default)]
    pub query_soundness_model: Option<QuerySoundnessModel>,
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CostContribution {
    pub feature: String,
    pub coefficient: f64,
    pub feature_value: f64,
    pub cu: f64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileScoreOutput {
    pub name: String,
    pub protocol_family: Option<String>,
    pub predicted_cu: f64,
    pub lower_cu: Option<f64>,
    pub upper_cu: Option<f64>,
    pub cu_budget_fraction: f64,
    pub proof_transport_pressure: f64,
    pub verification_core_cu: Option<f64>,
    pub transport_overhead_cu: Option<f64>,
    pub component_predicted_cu: Option<f64>,
    pub component_gap_vs_monolithic_cu: Option<f64>,
    pub feasible: bool,
    pub feasibility_reasons: Vec<String>,
    pub dominant_contributors: Vec<CostContribution>,
    #[serde(default)]
    pub query_soundness: Option<QuerySoundnessAssessment>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CoefficientBootstrapSummary {
    pub feature: String,
    pub samples: usize,
    pub mean: f64,
    pub p05: f64,
    pub p50: f64,
    pub p95: f64,
    pub sign_stable: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileSweepRecord {
    pub scenario_name: String,
    pub protocol_family: String,
    pub proof_bytes: u64,
    pub chunk_size: u64,
    pub query_count: u64,
    pub predicted_cu: f64,
    pub lower_cu: Option<f64>,
    pub upper_cu: Option<f64>,
    pub verification_core_cu: Option<f64>,
    pub transport_overhead_cu: Option<f64>,
    pub component_predicted_cu: Option<f64>,
    pub component_gap_vs_monolithic_cu: Option<f64>,
    pub cu_budget_fraction: f64,
    pub proof_transport_pressure: f64,
    pub feasible: bool,
    pub feasibility_reasons: Vec<String>,
    #[serde(default)]
    pub query_soundness: Option<QuerySoundnessAssessment>,
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RepoBaselineSummary {
    pub discovery_summary: String,
    pub existing_onchain_programs: Vec<String>,
    pub existing_verifier_entrypoints: Vec<String>,
    pub existing_benchmark_scripts: Vec<String>,
    pub existing_upload_path: Option<String>,
    pub existing_heap_handling: Option<String>,
    pub existing_patched_dependencies: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HistoricalBaseline {
    pub name: String,
    pub mean_cu: u64,
    pub max_cu: u64,
    pub run_count: u64,
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FailureObservation {
    pub boundary: String,
    pub status: String,
    pub details: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Phase1Summary {
    pub generated_at_utc: String,
    pub command: String,
    pub repo_baseline: RepoBaselineSummary,
    pub historical_baseline: HistoricalBaseline,
    pub measurement_count: usize,
    pub raw_artifacts: Vec<String>,
    pub measured_variables: Vec<String>,
    pub inferred_variables: Vec<String>,
    pub unknowns: Vec<String>,
    pub model: ModelComparison,
    #[serde(default)]
    pub verification_core_model: Option<ModelComparison>,
    #[serde(default)]
    pub transport_model: Option<ModelComparison>,
    #[serde(default)]
    pub coefficient_bootstrap: Vec<CoefficientBootstrapSummary>,
    #[serde(default)]
    pub sample_scores: Vec<ProfileScoreOutput>,
    #[serde(default)]
    pub circle_sweep: Vec<ProfileSweepRecord>,
    #[serde(default)]
    pub failure_modes: Vec<FailureObservation>,
    #[serde(default)]
    pub notes: Vec<String>,
}

#[derive(Clone)]
struct DesignMatrix {
    feature_names: Vec<String>,
    x: DMatrix<f64>,
    y: DVector<f64>,
}

fn successful_records<'a>(records: &'a [MeasurementRecord]) -> Vec<&'a MeasurementRecord> {
    records
        .iter()
        .filter(|record| record.status == MeasurementStatus::Success && record.actual_cu.is_some())
        .collect()
}

fn percentile(sorted: &[f64], quantile: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let scaled = quantile.clamp(0.0, 1.0) * (sorted.len().saturating_sub(1)) as f64;
    let lower = scaled.floor() as usize;
    let upper = scaled.ceil() as usize;
    if lower == upper {
        sorted[lower]
    } else {
        let weight = scaled - lower as f64;
        sorted[lower] * (1.0 - weight) + sorted[upper] * weight
    }
}

fn build_design_matrix(records: &[MeasurementRecord], candidates: &[&str]) -> Result<DesignMatrix> {
    let usable = successful_records(records);
    if usable.len() < 8 {
        bail!("need at least 8 successful measurements to fit a model");
    }

    let mut selected = Vec::new();
    for &name in candidates {
        let values: Vec<f64> = usable
            .iter()
            .map(|record| record.features.get(name).unwrap_or_default())
            .collect();
        let min = values
            .iter()
            .fold(f64::INFINITY, |acc, value| acc.min(*value));
        let max = values
            .iter()
            .fold(f64::NEG_INFINITY, |acc, value| acc.max(*value));
        if (max - min).abs() < f64::EPSILON {
            continue;
        }

        let trial = {
            let mut names = selected.clone();
            names.push(name.to_string());
            names
        };
        let x = matrix_for_features(&usable, &trial)?;
        let svd = x.clone().svd(false, false);
        let singular = svd.singular_values;
        let largest = singular.iter().copied().fold(0.0_f64, f64::max);
        let smallest = singular
            .iter()
            .copied()
            .filter(|value| *value > 1e-9)
            .fold(f64::INFINITY, f64::min);
        let condition = if smallest.is_finite() && smallest > 0.0 {
            largest / smallest
        } else {
            f64::INFINITY
        };
        if condition.is_finite() && condition < 1.0e8 {
            selected.push(name.to_string());
        }
    }

    if selected.is_empty() {
        bail!("all candidate features were dropped");
    }

    let x = matrix_for_features(&usable, &selected)?;
    let y = DVector::from_iterator(
        usable.len(),
        usable
            .iter()
            .map(|record| record.actual_cu.unwrap_or_default() as f64),
    );
    let mut feature_names = vec!["intercept".to_string()];
    feature_names.extend(selected);
    Ok(DesignMatrix {
        feature_names,
        x,
        y,
    })
}

fn fit_additive_model_with_candidates(
    records: &[MeasurementRecord],
    candidates: &[&str],
) -> Result<ModelComparison> {
    let original_candidates = candidates.to_vec();
    let mut candidates = original_candidates.clone();
    loop {
        let design = build_design_matrix(records, &candidates)?;
        let base_weights = vec![1.0; design.x.nrows()];
        let ols = fit_internal(
            &design,
            &original_candidates,
            "ordinary_least_squares",
            &base_weights,
            vec!["Chosen to keep the initial model additive and interpretable.".to_string()],
        )?;

        let mut weights = vec![1.0; design.x.nrows()];
        for _ in 0..12 {
            let (_, residuals, _) = weighted_least_squares(&design.x, &design.y, &weights)?;
            let mut abs_residuals: Vec<f64> = residuals.iter().map(|value| value.abs()).collect();
            abs_residuals.sort_by(f64::total_cmp);
            let scale = percentile(&abs_residuals, 0.5).max(1.0);
            for (weight, residual) in weights.iter_mut().zip(residuals.iter()) {
                let cutoff = 1.345 * scale;
                let abs = residual.abs();
                *weight = if abs <= cutoff { 1.0 } else { cutoff / abs };
            }
        }
        let huber = fit_internal(
            &design,
            &original_candidates,
            "huber_irls",
            &weights,
            vec![
                "Huber IRLS down-weights outliers from local validator noise or allocator jitter."
                    .to_string(),
            ],
        )?;

        let chosen = if huber.metrics.p95_abs_error <= ols.metrics.p95_abs_error * 1.05 {
            huber.clone()
        } else {
            ols.clone()
        };

        let negative_features = chosen
            .selected_features
            .iter()
            .filter_map(|name| {
                chosen
                    .coefficients
                    .get(name)
                    .and_then(|coef| (coef.estimate < 0.0).then(|| name.clone()))
            })
            .collect::<Vec<_>>();
        if negative_features.is_empty() || candidates.len() <= 3 {
            return Ok(ModelComparison { chosen, ols, huber });
        }
        candidates.retain(|name| !negative_features.iter().any(|feature| feature == name));
    }
}

fn matrix_for_features(
    records: &[&MeasurementRecord],
    features: &[String],
) -> Result<DMatrix<f64>> {
    let rows = records.len();
    let cols = features.len() + 1;
    let mut values = Vec::with_capacity(rows * cols);
    for record in records {
        values.push(1.0);
        for name in features {
            values.push(record.features.get(name)?);
        }
    }
    Ok(DMatrix::from_row_slice(rows, cols, &values))
}

fn weighted_least_squares(
    x: &DMatrix<f64>,
    y: &DVector<f64>,
    weights: &[f64],
) -> Result<(DVector<f64>, DVector<f64>, Option<Vec<f64>>)> {
    let sqrt_weights: Vec<f64> = weights.iter().map(|weight| weight.sqrt()).collect();
    let mut wx = x.clone();
    let mut wy = y.clone();
    for row in 0..x.nrows() {
        let scale = sqrt_weights[row];
        for col in 0..x.ncols() {
            wx[(row, col)] *= scale;
        }
        wy[row] *= scale;
    }

    let svd = wx.clone().svd(true, true);
    let beta = svd
        .solve(&wy, 1.0e-9)
        .map_err(|_| anyhow!("least-squares solve failed"))?;
    let predictions = x * beta.clone();
    let residuals = y - predictions;

    let dof = (x.nrows() as isize - x.ncols() as isize).max(1) as f64;
    let weighted_sse = residuals
        .iter()
        .zip(weights.iter())
        .map(|(residual, weight)| residual.powi(2) * weight)
        .sum::<f64>();
    let sigma2 = weighted_sse / dof;

    let xtwx = wx.transpose() * wx;
    let stderr = xtwx.try_inverse().map(|inverse| {
        (0..inverse.nrows())
            .map(|idx| (inverse[(idx, idx)] * sigma2).max(0.0).sqrt())
            .collect::<Vec<_>>()
    });

    Ok((beta, residuals, stderr))
}

fn fit_internal(
    design: &DesignMatrix,
    candidates: &[&str],
    method: &str,
    weights: &[f64],
    notes: Vec<String>,
) -> Result<FittedCostModel> {
    let (beta, residuals, stderr) = weighted_least_squares(&design.x, &design.y, weights)?;
    let predictions = &design.x * beta.clone();
    let mut abs_errors: Vec<f64> = residuals.iter().map(|value| value.abs()).collect();
    abs_errors.sort_by(f64::total_cmp);

    let rmse =
        (residuals.iter().map(|value| value.powi(2)).sum::<f64>() / residuals.len() as f64).sqrt();
    let mae = abs_errors.iter().sum::<f64>() / abs_errors.len() as f64;
    let p95_abs_error = percentile(&abs_errors, 0.95);
    let max_abs_error = abs_errors.last().copied().unwrap_or_default();

    let mean_y = design.y.iter().sum::<f64>() / design.y.len() as f64;
    let total_variance = design
        .y
        .iter()
        .map(|value| (value - mean_y).powi(2))
        .sum::<f64>();
    let residual_variance = residuals.iter().map(|value| value.powi(2)).sum::<f64>();
    let r_squared = if total_variance > 0.0 {
        Some(1.0 - residual_variance / total_variance)
    } else {
        None
    };

    let svd = design.x.clone().svd(false, false);
    let singular = svd.singular_values;
    let largest = singular.iter().copied().fold(0.0_f64, f64::max);
    let smallest = singular
        .iter()
        .copied()
        .filter(|value| *value > 1e-9)
        .fold(f64::INFINITY, f64::min);
    let condition_number = if smallest.is_finite() && smallest > 0.0 {
        Some(largest / smallest)
    } else {
        None
    };

    let mut coefficients = CostCoefficients::default();
    for (idx, name) in design.feature_names.iter().enumerate() {
        let estimate = CoefficientEstimate {
            estimate: beta[idx],
            stderr: stderr.as_ref().and_then(|values| values.get(idx).copied()),
            rationale: if idx == 0 {
                "baseline transaction/program overhead".to_string()
            } else {
                format!("fitted from Phase 1 measurement surface via {method}")
            },
        };
        coefficients.set(name, estimate)?;
    }

    let dropped_features = candidates
        .iter()
        .filter(|name| !design.feature_names.iter().any(|feature| feature == **name))
        .map(|name| (*name).to_string())
        .collect::<Vec<_>>();

    let _ = predictions;
    Ok(FittedCostModel {
        method: method.to_string(),
        selected_features: design.feature_names.iter().skip(1).cloned().collect(),
        dropped_features,
        coefficients,
        metrics: ModelMetrics {
            record_count: design.x.nrows(),
            rmse,
            mae,
            p95_abs_error,
            max_abs_error,
            r_squared,
        },
        uncertainty_rmse: rmse,
        condition_number,
        notes,
    })
}

pub fn fit_additive_model(records: &[MeasurementRecord]) -> Result<ModelComparison> {
    fit_additive_model_with_candidates(records, CANDIDATE_FEATURES)
}

pub fn fit_additive_model_for_features(
    records: &[MeasurementRecord],
    candidates: &[&str],
) -> Result<ModelComparison> {
    fit_additive_model_with_candidates(records, candidates)
}

fn predict_with_contributions(
    model: &FittedCostModel,
    features: &CostFeatures,
) -> Result<(f64, Vec<CostContribution>)> {
    let intercept = model
        .coefficients
        .intercept
        .as_ref()
        .map(|coef| coef.estimate)
        .unwrap_or_default();
    let mut predicted = intercept;
    let mut contributions = Vec::new();
    for name in &model.selected_features {
        let feature_value = features.get(name)?;
        let coefficient = match model.coefficients.get(name) {
            Some(value) => value.estimate,
            None => continue,
        };
        let cu = feature_value * coefficient;
        predicted += cu;
        contributions.push(CostContribution {
            feature: name.clone(),
            coefficient,
            feature_value,
            cu,
        });
    }
    contributions.sort_by(|lhs, rhs| rhs.cu.abs().total_cmp(&lhs.cu.abs()));
    Ok((predicted, contributions))
}

fn subtract_transport_features(
    full: &CostFeatures,
    transport: &TransportCostFeatures,
) -> CostFeatures {
    let mut core = full.clone();
    core.sha_calls = core.sha_calls.saturating_sub(transport.sha_calls);
    core.sha_bytes = core.sha_bytes.saturating_sub(transport.sha_bytes);
    core.upload_bytes = core.upload_bytes.saturating_sub(transport.upload_bytes);
    core.upload_chunks = core.upload_chunks.saturating_sub(transport.upload_chunks);
    core
}

fn profile_upload_bytes(input: &ProfileScoreInput) -> u64 {
    input
        .transport
        .upload_bytes
        .max(input.features.upload_bytes)
}

fn whir_query_log_1_delta(log_inv_rate: u32, capacity_bound: bool) -> f64 {
    let log_inv_rate_f = log_inv_rate as f64;
    let rate = 1.0 / ((1_u64 << log_inv_rate) as f64);
    let log_eta = if capacity_bound {
        -(log_inv_rate_f + std::f64::consts::LOG2_10 + 1.0)
    } else {
        -(0.5 * log_inv_rate_f + std::f64::consts::LOG2_10 + 1.0)
    };
    let eta = 2_f64.powf(log_eta);
    let delta = if capacity_bound {
        1.0 - rate - eta
    } else {
        1.0 - rate.sqrt() - eta
    };
    (1.0 - delta).log2()
}

pub fn assess_query_soundness(model: &QuerySoundnessModel) -> QuerySoundnessAssessment {
    match model {
        QuerySoundnessModel::Fri {
            query_count,
            log_blowup,
            query_proof_of_work_bits,
            target_bits,
            sources,
            notes,
        } => {
            let lower_bits = 0.5 * (*log_blowup as f64) * (*query_count as f64)
                + *query_proof_of_work_bits as f64;
            let upper_bits =
                (*log_blowup as f64) * (*query_count as f64) + *query_proof_of_work_bits as f64;
            let mut assessment_notes = vec![
                "Lower bound uses the proven FRI query term rate^(q/2).".to_string(),
                "Upper bound uses the conjectured ethSTARK-style rate^q term used by p3-fri."
                    .to_string(),
            ];
            assessment_notes.extend(notes.iter().cloned());
            QuerySoundnessAssessment {
                model: "fri_query_soundness".to_string(),
                query_count: *query_count,
                target_bits: *target_bits,
                lower_bits,
                lower_assumption: "fri_proven_rate_pow_q_over_2".to_string(),
                upper_bits: Some(upper_bits),
                upper_assumption: Some("ethstark_conjectured_rate_pow_q".to_string()),
                meets_target: lower_bits >= *target_bits,
                notes: assessment_notes,
                sources: sources.clone(),
            }
        }
        QuerySoundnessModel::Whir {
            query_count,
            log_inv_rate,
            pow_bits,
            target_bits,
            sources,
            notes,
        } => {
            let lower_bits = -(*query_count as f64) * whir_query_log_1_delta(*log_inv_rate, false)
                + *pow_bits as f64;
            let upper_bits = -(*query_count as f64) * whir_query_log_1_delta(*log_inv_rate, true)
                + *pow_bits as f64;
            let mut assessment_notes = vec![
                "Lower bound uses the Johnson-bound query term with eta = sqrt(rho)/20 from the official Plonky3 WHIR soundness model.".to_string(),
                "Upper bound uses the capacity-bound query term with eta = rho/20 from the same model.".to_string(),
                "This assessment interprets q as the explicit proximity-query count and adds the configured WHIR proof-of-work budget as an independent additive term.".to_string(),
                "It still omits OOD and folding terms, so it remains a query-controlled security screen rather than a full WHIR security proof.".to_string(),
            ];
            assessment_notes.extend(notes.iter().cloned());
            QuerySoundnessAssessment {
                model: "whir_query_soundness".to_string(),
                query_count: *query_count,
                target_bits: *target_bits,
                lower_bits,
                lower_assumption: "whir_johnson_bound_query_term".to_string(),
                upper_bits: Some(upper_bits),
                upper_assumption: Some("whir_capacity_bound_query_term".to_string()),
                meets_target: lower_bits >= *target_bits,
                notes: assessment_notes,
                sources: sources.clone(),
            }
        }
    }
}

pub fn score_profile_with_components(
    model: &FittedCostModel,
    verification_core_model: Option<&FittedCostModel>,
    transport_model: Option<&FittedCostModel>,
    limits: &SvmLimits,
    input: &ProfileScoreInput,
) -> Result<ProfileScoreOutput> {
    let (predicted, contributions) = predict_with_contributions(model, &input.features)?;
    let dominant_contributors = contributions.into_iter().take(3).collect::<Vec<_>>();

    let lower = (predicted - model.uncertainty_rmse).max(0.0);
    let upper = predicted + model.uncertainty_rmse;
    let proof_transport_pressure =
        profile_upload_bytes(input) as f64 / limits.max_transaction_bytes as f64;

    let verification_core_cu = verification_core_model
        .map(|component_model| {
            let core_features = subtract_transport_features(&input.features, &input.transport);
            predict_with_contributions(component_model, &core_features).map(|(value, _)| value)
        })
        .transpose()?;
    let transport_overhead_cu = transport_model
        .map(|component_model| {
            let transport_features = input.transport.as_cost_features();
            predict_with_contributions(component_model, &transport_features).map(|(value, _)| value)
        })
        .transpose()?;
    let component_predicted_cu = verification_core_cu
        .zip(transport_overhead_cu)
        .map(|(core, transport)| core + transport);
    let component_gap_vs_monolithic_cu =
        component_predicted_cu.map(|component_total| component_total - predicted);

    let mut feasibility_reasons = Vec::new();
    if predicted > limits.max_compute_units_per_tx as f64 {
        feasibility_reasons.push("predicted CU exceeds the transaction compute budget".to_string());
    }
    if input.features.heap_frame_bytes_requested > limits.max_heap_frame_bytes {
        feasibility_reasons.push("requested heap frame exceeds current SVM limit".to_string());
    }
    if input.features.upload_chunks == 0
        && profile_upload_bytes(input) > limits.max_transaction_bytes
    {
        feasibility_reasons
            .push("upload bytes imply chunking but upload_chunks is zero".to_string());
    }
    let query_soundness = input
        .query_soundness_model
        .as_ref()
        .map(assess_query_soundness);
    if let Some(soundness) = &query_soundness {
        if !soundness.meets_target {
            feasibility_reasons.push(format!(
                "query-controlled soundness lower bound {:.1} bits is below the {:.1}-bit target",
                soundness.lower_bits, soundness.target_bits
            ));
        }
    }

    Ok(ProfileScoreOutput {
        name: input.name.clone(),
        protocol_family: input.protocol_family.clone(),
        predicted_cu: predicted,
        lower_cu: Some(lower),
        upper_cu: Some(upper),
        cu_budget_fraction: predicted / limits.max_compute_units_per_tx as f64,
        proof_transport_pressure,
        verification_core_cu,
        transport_overhead_cu,
        component_predicted_cu,
        component_gap_vs_monolithic_cu,
        feasible: feasibility_reasons.is_empty(),
        feasibility_reasons,
        dominant_contributors,
        query_soundness,
    })
}

pub fn score_profile(
    model: &FittedCostModel,
    limits: &SvmLimits,
    input: &ProfileScoreInput,
) -> Result<ProfileScoreOutput> {
    score_profile_with_components(model, None, None, limits, input)
}

#[derive(Clone)]
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 {
                0x9E37_79B9_7F4A_7C15
            } else {
                seed
            },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn next_index(&mut self, upper: usize) -> usize {
        (self.next_u64() as usize) % upper.max(1)
    }
}

pub fn bootstrap_coefficients(
    records: &[MeasurementRecord],
    candidates: &[&str],
    iterations: usize,
    seed: u64,
) -> Result<Vec<CoefficientBootstrapSummary>> {
    let successful = successful_records(records)
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    if successful.len() < 8 {
        bail!("need at least 8 successful measurements to bootstrap coefficients");
    }

    let base = fit_additive_model_with_candidates(&successful, candidates)?;
    let tracked = std::iter::once("intercept".to_string())
        .chain(base.chosen.selected_features.iter().cloned())
        .collect::<Vec<_>>();
    let mut samples = BTreeMap::<String, Vec<f64>>::new();
    for feature in &tracked {
        samples.insert(feature.clone(), Vec::new());
    }

    let mut rng = XorShift64::new(seed);
    for _ in 0..iterations {
        let mut sample = Vec::with_capacity(successful.len());
        for _ in 0..successful.len() {
            sample.push(successful[rng.next_index(successful.len())].clone());
        }
        let fitted = match fit_additive_model_with_candidates(&sample, candidates) {
            Ok(value) => value,
            Err(_) => continue,
        };
        for feature in &tracked {
            if let Some(coef) = fitted.chosen.coefficients.get(feature) {
                if let Some(values) = samples.get_mut(feature) {
                    values.push(coef.estimate);
                }
            }
        }
    }

    let mut summaries = Vec::new();
    for feature in tracked {
        let mut values = samples.remove(&feature).unwrap_or_default();
        if values.is_empty() {
            continue;
        }
        values.sort_by(f64::total_cmp);
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        let sign_stable =
            values.iter().all(|value| *value >= 0.0) || values.iter().all(|value| *value <= 0.0);
        summaries.push(CoefficientBootstrapSummary {
            feature,
            samples: values.len(),
            mean,
            p05: percentile(&values, 0.05),
            p50: percentile(&values, 0.50),
            p95: percentile(&values, 0.95),
            sign_stable,
        });
    }
    Ok(summaries)
}

pub fn render_markdown_report(summary: &Phase1Summary) -> String {
    let model = &summary.model.chosen;
    let coefficients = &model.coefficients;
    let mut lines = Vec::new();
    lines.push("# Phase 1 Cost Model".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Build a machine-calibrated Phase 1 measurement stack for transparent-proof verification costs on Solana, with explicit separation between directly measured surfaces, structure-derived features, and proxy estimates.".to_string());
    lines.push(String::new());
    lines.push("## Repo Baseline".to_string());
    lines.push(summary.repo_baseline.discovery_summary.clone());
    lines.push(format!(
        "Historical baseline preserved from prior PoC context: `verify_stark` mean {} CU, max {} CU over {} runs.",
        summary.historical_baseline.mean_cu,
        summary.historical_baseline.max_cu,
        summary.historical_baseline.run_count
    ));
    lines.push(String::new());
    lines.push("## Methodology".to_string());
    lines.push("Phase 1 uses a local `solana-test-validator` plus SBF probe program to isolate marginal surfaces. CU is taken from transaction simulation. Feature attributions are stored per record as `direct_measurement`, `derived_structure`, or `estimated_proxy`.".to_string());
    lines.push(String::new());
    lines.push("## Benchmark Surfaces".to_string());
    lines.push("- Hash syscall: hash call count and hashed bytes.".to_string());
    lines.push("- Merkle path: total authentication levels across paths.".to_string());
    lines.push(
        "- Proof parsing: proof bytes and segment count using fixed-header vs varint framing."
            .to_string(),
    );
    lines.push("- Field arithmetic: add/sub, mul, inversion, extension-mul proxies.".to_string());
    lines.push("- Heap frame: requested heap and touched scratch bytes.".to_string());
    lines.push(
        "- Account I/O: readonly and writable account counts plus bytes read/written.".to_string(),
    );
    lines.push(
        "- Upload path: chunk count, bytes uploaded, optional rolling-hash checks.".to_string(),
    );
    lines.push(
        "- Synthetic verifier: coarse aggregate profile assembled from the surfaces above."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Measured Variables".to_string());
    for item in &summary.measured_variables {
        lines.push(format!("- {item}"));
    }
    lines.push(String::new());
    lines.push("## Inferred Variables".to_string());
    for item in &summary.inferred_variables {
        lines.push(format!("- {item}"));
    }
    lines.push(String::new());
    lines.push("## Fitted Model".to_string());
    lines.push(format!(
        "Chosen fit: `{}` over {} successful records. RMSE {:.1} CU, MAE {:.1} CU, p95 abs error {:.1} CU.",
        model.method,
        model.metrics.record_count,
        model.metrics.rmse,
        model.metrics.mae,
        model.metrics.p95_abs_error
    ));
    for name in ["intercept"]
        .into_iter()
        .chain(CANDIDATE_FEATURES.iter().copied())
    {
        if let Some(coef) = coefficients.get(name) {
            lines.push(format!(
                "- `{name}`: {:.6} CU per unit{}",
                coef.estimate,
                coef.stderr
                    .map(|stderr| format!(" (stderr {:.6})", stderr))
                    .unwrap_or_default()
            ));
        }
    }
    if let Some(core_model) = &summary.verification_core_model {
        lines.push(format!(
            "- Verification-core secondary fit: `{}` with RMSE {:.1} CU and p95 abs error {:.1} CU.",
            core_model.chosen.method,
            core_model.chosen.metrics.rmse,
            core_model.chosen.metrics.p95_abs_error
        ));
    }
    if let Some(transport_model) = &summary.transport_model {
        lines.push(format!(
            "- Transport secondary fit: `{}` with RMSE {:.1} CU and p95 abs error {:.1} CU.",
            transport_model.chosen.method,
            transport_model.chosen.metrics.rmse,
            transport_model.chosen.metrics.p95_abs_error
        ));
    }
    lines.push(String::new());
    lines.push("## Prediction Error".to_string());
    lines.push(format!(
        "OLS RMSE {:.1} CU vs Huber RMSE {:.1} CU. Chosen model uncertainty band uses ±{:.1} CU as a first-pass residual envelope.",
        summary.model.ols.metrics.rmse,
        summary.model.huber.metrics.rmse,
        model.uncertainty_rmse
    ));
    if !summary.coefficient_bootstrap.is_empty() {
        lines.push(
            "Bootstrap summaries for selected coefficients (deterministic resampling):".to_string(),
        );
        for item in &summary.coefficient_bootstrap {
            lines.push(format!(
                "- `{}`: mean {:.3}, p05 {:.3}, p50 {:.3}, p95 {:.3}, sign_stable={}",
                item.feature, item.mean, item.p05, item.p50, item.p95, item.sign_stable
            ));
        }
    }
    lines.push(String::new());
    lines.push("## Dominant Cost Drivers".to_string());
    for score in &summary.sample_scores {
        let drivers = score
            .dominant_contributors
            .iter()
            .map(|item| format!("{} ({:.1} CU)", item.feature, item.cu))
            .collect::<Vec<_>>()
            .join(", ");
        let decomposition = match (score.verification_core_cu, score.transport_overhead_cu) {
            (Some(core), Some(transport)) => {
                format!("; core {:.1} CU, transport {:.1} CU", core, transport)
            }
            _ => String::new(),
        };
        lines.push(format!("- `{}`: {}{}", score.name, drivers, decomposition));
    }
    lines.push(String::new());
    lines.push("## Safe Operating Region".to_string());
    lines.push("Profiles are provisionally comfortable when predicted CU stays below roughly 85% of the 1.4M cap, upload transport pressure stays below 1.0 per transaction chunk, and requested heap stays below 256 KiB.".to_string());
    if !summary.circle_sweep.is_empty() {
        let feasible = summary
            .circle_sweep
            .iter()
            .filter(|scenario| scenario.feasible)
            .count();
        if let Some(best) = summary
            .circle_sweep
            .iter()
            .min_by(|lhs, rhs| lhs.predicted_cu.total_cmp(&rhs.predicted_cu))
        {
            lines.push(format!(
                "Circle sweep explored {} scenarios; {} were feasible under current limits. Lowest predicted point was `{}` at {:.1} CU.",
                summary.circle_sweep.len(),
                feasible,
                best.scenario_name,
                best.predicted_cu
            ));
        }
    }
    lines.push(String::new());
    lines.push("## Failure Modes".to_string());
    for failure in &summary.failure_modes {
        lines.push(format!(
            "- {}: {} ({})",
            failure.boundary, failure.status, failure.details
        ));
    }
    lines.push(String::new());
    lines.push("## Limitations / Confounders".to_string());
    lines.push("- No production verifier was present in the repo, so coarse end-to-end extraction targets a synthetic verifier probe rather than a semantic proof verifier.".to_string());
    lines.push(
        "- Validator version drift can move CU, allocator behavior, and syscall pricing."
            .to_string(),
    );
    lines.push(
        "- Local validator cache warmth and account-layout choices can shift measurements."
            .to_string(),
    );
    lines.push(
        "- Field-op counts are microkernel proxies, not dynamic counts from a live verifier."
            .to_string(),
    );
    lines.push("- Heap behavior depends on the Solana allocator and the request-heap-frame instruction; this stack measures observed transaction cost, not allocator internals.".to_string());
    lines.push(String::new());
    lines.push("## Recommended Next Experiments".to_string());
    lines.push("- Replace the synthetic verifier probe with a real verifier path while preserving the current feature schema.".to_string());
    lines.push("- Run orthogonal sweeps that isolate transport bytes/chunks from core hash and Merkle structure.".to_string());
    lines.push(
        "- Add version-pinned cross-validator runs to quantify Agave/Solana drift.".to_string(),
    );
    lines.push("- Score spend-circuit-shaped profiles once statement-specific field-op proxies are available.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `{}`._",
        summary.generated_at_utc, summary.command
    ));
    lines.join("\n")
}

pub fn load_summary(path: &std::path::Path) -> Result<Phase1Summary> {
    let bytes =
        std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
    let summary = serde_json::from_slice(&bytes)
        .with_context(|| format!("failed to parse {}", path.display()))?;
    Ok(summary)
}

pub fn load_profile_input(path: &std::path::Path) -> Result<ProfileScoreInput> {
    let bytes =
        std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
    let extension = path
        .extension()
        .and_then(|value| value.to_str())
        .unwrap_or_default();
    let profile = match extension {
        "yaml" | "yml" => serde_yaml::from_slice(&bytes)
            .with_context(|| format!("failed to parse {}", path.display()))?,
        _ => serde_json::from_slice(&bytes)
            .with_context(|| format!("failed to parse {}", path.display()))?,
    };
    Ok(profile)
}

pub fn new_measurement_id(prefix: &str, repetition: u32) -> String {
    format!(
        "{prefix}-{}-{repetition:02}",
        Utc::now().format("%Y%m%dT%H%M%S")
    )
}
