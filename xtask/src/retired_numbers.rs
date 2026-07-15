use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct Allowlist {
    schema: String,
    files: Vec<String>,
    patterns: Vec<Pattern>,
    allowed_occurrences: Vec<AllowedOccurrence>,
}

#[derive(Deserialize)]
struct Pattern {
    id: String,
    needles: Vec<String>,
}

#[derive(Deserialize)]
struct AllowedOccurrence {
    path: String,
    pattern_id: String,
    line_contains: String,
    reason: String,
}

#[derive(Serialize)]
pub(crate) struct LintSummary {
    schema: &'static str,
    allowlist_schema: String,
    pub(crate) files_scanned: usize,
    pub(crate) retired_occurrences_allowed: usize,
    violations: Vec<String>,
}

fn workspace_root() -> Result<PathBuf> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("xtask has no workspace parent")
}

fn discover_markdown(dir: &Path, root: &Path, paths: &mut Vec<String>) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("scan {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            discover_markdown(&path, root, paths)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("md") {
            let relative = path
                .strip_prefix(root)
                .with_context(|| format!("{} is outside {}", path.display(), root.display()))?;
            paths.push(relative.to_string_lossy().replace('\\', "/"));
        }
    }
    Ok(())
}

fn contains_needle(haystack: &str, needle: &str) -> bool {
    haystack.match_indices(needle).any(|(start, _)| {
        let end = start + needle.len();
        let starts_alphanumeric = needle
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_alphanumeric());
        let ends_alphanumeric = needle
            .chars()
            .next_back()
            .is_some_and(|character| character.is_ascii_alphanumeric());
        let left_is_alphanumeric = haystack[..start]
            .chars()
            .next_back()
            .is_some_and(|character| character.is_ascii_alphanumeric());
        let right_is_alphanumeric = haystack[end..]
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_alphanumeric());
        (!starts_alphanumeric || !left_is_alphanumeric)
            && (!ends_alphanumeric || !right_is_alphanumeric)
    })
}

pub(crate) fn lint_retired_numbers() -> Result<LintSummary> {
    let root = workspace_root()?;
    let allowlist_path = root.join("xtask/fixtures/retired_numbers_allowlist.json");
    let allowlist: Allowlist = serde_json::from_str(
        &fs::read_to_string(&allowlist_path)
            .with_context(|| format!("read {}", allowlist_path.display()))?,
    )
    .with_context(|| format!("parse {}", allowlist_path.display()))?;

    let mut files = allowlist.files.clone();
    discover_markdown(&root.join("docs"), &root, &mut files)?;
    files.sort();
    files.dedup();

    let mut allowed = 0_usize;
    let mut violations = Vec::new();
    for path in &files {
        let full = root.join(path);
        let text = fs::read_to_string(&full)
            .with_context(|| format!("read quote-facing file {}", full.display()))?;
        for (line_index, line) in text.lines().enumerate() {
            for pattern in &allowlist.patterns {
                if !pattern
                    .needles
                    .iter()
                    .any(|needle| contains_needle(line, needle))
                {
                    continue;
                }
                let matching_allowances = allowlist.allowed_occurrences.iter().filter(|entry| {
                    entry.path == *path
                        && entry.pattern_id == pattern.id
                        && line.contains(&entry.line_contains)
                });
                let mut reasons = matching_allowances.map(|entry| entry.reason.as_str());
                if reasons.next().is_some() {
                    allowed += 1;
                } else {
                    violations.push(format!(
                        "{}:{} [{}] {}",
                        path,
                        line_index + 1,
                        pattern.id,
                        line.trim()
                    ));
                }
            }
        }
    }

    let summary = LintSummary {
        schema: "aspis.retired_quote_numbers_lint.v1",
        allowlist_schema: allowlist.schema,
        files_scanned: files.len(),
        retired_occurrences_allowed: allowed,
        violations,
    };
    if !summary.violations.is_empty() {
        bail!(
            "retired quote-facing numbers escaped the structured allowlist:\n{}",
            summary.violations.join("\n")
        );
    }
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::contains_needle;

    #[test]
    fn retired_number_match_respects_numeric_token_boundaries() {
        assert!(contains_needle("the 104 bits line", "104 bits"));
        assert!(contains_needle("2^-104 + epsilon", "2^-104"));
        assert!(!contains_needle("T6 is 110.7104 bits", "104 bits"));
        assert!(!contains_needle("q450 is different", "q45"));
    }

    #[test]
    fn quote_facing_retired_numbers_are_scoped() {
        super::lint_retired_numbers().unwrap();
    }
}
