use std::path::PathBuf;

use build_fs_tree::{Build, MergeableFileSystemTree};
use clap::Parser;

use sm83_zklean_extractor::bitvec_bridge::Sm83BitVecBridge;
use sm83_zklean_extractor::constraints::{Sm83Constraints, Sm83StepInputs};
use sm83_zklean_extractor::instructions::Sm83Instructions;
use sm83_zklean_extractor::lookups::Sm83LookupTables;
use sm83_zklean_extractor::modules::{make_sm83_zk_lean_package, AsModule, FSError};
use sm83_zklean_extractor::proofs_gen::Sm83Proofs;
use sm83_zklean_extractor::instruction_proofs_gen::Sm83InstructionProofs;
use sm83_zklean_extractor::spec_gen::Sm83Spec;
use sm83_zklean_extractor::tests_gen::Sm83Tests;

#[derive(Parser)]
#[command(version, about = "Extract SM83 ALU operations into a Lean4/zkLean package")]
struct Args {
    /// Path to save SM83 zkLean package to
    #[arg(short, long)]
    package_path: PathBuf,

    /// Don't complain if the directory already exists (will clobber colliding files)
    #[arg(short, long, default_value_t = false)]
    overwrite: bool,
}

fn extract_modules() -> Vec<Box<dyn AsModule>> {
    vec![
        Box::new(Sm83LookupTables::extract()),
        Box::new(Sm83Instructions::extract()),
        Box::new(Sm83StepInputs::extract()),
        Box::new(Sm83Constraints::extract()),
        Box::new(Sm83Tests::extract()),
        Box::new(Sm83Spec::extract()),
        Box::new(Sm83BitVecBridge::extract()),
        Box::new(Sm83Proofs::extract()),
        Box::new(Sm83InstructionProofs::extract()),
    ]
}

fn main() -> Result<(), FSError> {
    let args = Args::parse();
    let modules = extract_modules();
    let tree = make_sm83_zk_lean_package(modules)?;

    if args.overwrite {
        MergeableFileSystemTree::from(tree)
            .build(&args.package_path)
            .map_err(|e| FSError::TemplateError(format!("{e:?}")))?;
    } else {
        tree.build(&args.package_path)
            .map_err(|e| FSError::TemplateError(format!("{e:?}")))?;
    }

    println!("Created SM83 zkLean package at {:?}", args.package_path);
    Ok(())
}
