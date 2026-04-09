use build_fs_tree::{dir, file, serde_yaml, FileSystemTree};

/// A module to write to the SM83 zkLean package.
pub struct Module {
    /// The name of the module. The filename will become `SM83/{name}.lean`.
    pub name: String,
    /// A list of modules to import.
    pub imports: Vec<String>,
    /// The contents of the module formatted as Lean4 code.
    pub contents: Vec<u8>,
}

/// Trait for objects that can be converted to `Module`.
pub trait AsModule {
    fn as_module(&self) -> std::io::Result<Module>;
}

type FSTree = FileSystemTree<String, Vec<u8>>;
type FSResult<T> = Result<T, FSError>;

#[derive(Debug)]
pub enum FSError {
    IoError(std::io::Error),
    BuildError(std::io::Error),
    YamlError(serde_yaml::Error),
    TemplateError(String),
}

impl From<std::io::Error> for FSError {
    fn from(e: std::io::Error) -> Self {
        FSError::IoError(e)
    }
}


impl From<serde_yaml::Error> for FSError {
    fn from(e: serde_yaml::Error) -> Self {
        FSError::YamlError(e)
    }
}

const DEFAULT_TEMPLATE_YAML: &str = include_str!(env!("TEMPLATE_YAML_PATH"));

pub fn make_sm83_zk_lean_package(
    modules: Vec<Box<dyn AsModule>>,
) -> FSResult<FSTree> {
    let mut builder: FSTree =
        serde_yaml::from_str(DEFAULT_TEMPLATE_YAML).map_err(FSError::from)?;

    let sm83_dir = builder
        .dir_content_mut()
        .ok_or(FSError::TemplateError("root is not a directory".into()))?
        .entry(String::from("SM83"))
        .or_insert(dir! {})
        .dir_content_mut()
        .ok_or(FSError::TemplateError("SM83 is not a directory".into()))?;

    for module in modules {
        let module = module.as_module()?;
        let contents_with_imports: Vec<u8> = module
            .imports
            .into_iter()
            .flat_map(|i| format!("import {i}\n").bytes().collect::<Vec<u8>>())
            .chain(vec![b'\n'])
            .chain(module.contents)
            .collect();
        let _ = sm83_dir.insert(
            format!("{}.lean", module.name),
            file!(contents_with_imports),
        );
    }

    Ok(builder)
}
