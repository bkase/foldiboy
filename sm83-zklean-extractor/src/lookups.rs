//! Generates the SM83/LookupTables.lean module.

use crate::mle::table_to_lean;
use crate::modules::{AsModule, Module};
use crate::tables::Sm83Table;

pub struct Sm83LookupTables {
    tables: Vec<Sm83Table>,
}

impl Sm83LookupTables {
    pub fn extract() -> Self {
        Self {
            tables: Sm83Table::all(),
        }
    }
}

impl AsModule for Sm83LookupTables {
    fn as_module(&self) -> std::io::Result<Module> {
        let mut contents = Vec::new();

        for table in &self.tables {
            let lean = table_to_lean(*table);
            contents.extend_from_slice(lean.as_bytes());
            contents.push(b'\n');
        }

        Ok(Module {
            name: "LookupTables".into(),
            imports: vec!["zkLean".into(), "SM83.Util".into()],
            contents,
        })
    }
}
