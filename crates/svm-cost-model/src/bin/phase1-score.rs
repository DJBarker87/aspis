use std::path::PathBuf;

use anyhow::Result;
use svm_cost_model::{load_profile_input, load_summary, score_profile_with_components, SvmLimits};

fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let summary_path = PathBuf::from(args.next().expect("summary json path required"));
    let profile_path = PathBuf::from(args.next().expect("profile yaml/json path required"));

    let summary = load_summary(&summary_path)?;
    let profile = load_profile_input(&profile_path)?;
    let score = score_profile_with_components(
        &summary.model.chosen,
        summary
            .verification_core_model
            .as_ref()
            .map(|model| &model.chosen),
        summary.transport_model.as_ref().map(|model| &model.chosen),
        &SvmLimits::default(),
        &profile,
    )?;
    println!("{}", serde_json::to_string_pretty(&score)?);
    Ok(())
}
