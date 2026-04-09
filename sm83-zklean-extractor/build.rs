use build_fs_tree::FileSystemTree;
use std::path::Path;

fn main() {
    let template_dir = Path::new("package-template");
    let tree = read_fs_tree_recursively(template_dir);
    let yaml = serde_yaml::to_string(&tree).expect("failed to serialize template");

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let yaml_path = Path::new(&out_dir).join("template.yaml");
    std::fs::write(&yaml_path, yaml).expect("failed to write template yaml");

    println!("cargo:rustc-env=TEMPLATE_YAML_PATH={}", yaml_path.display());
    println!("cargo:rerun-if-changed=package-template");
}

fn read_fs_tree_recursively(path: &Path) -> FileSystemTree<String, Vec<u8>> {
    if path.is_file() {
        let contents = std::fs::read(path).unwrap_or_default();
        FileSystemTree::File(contents)
    } else if path.is_dir() {
        let mut entries = std::collections::BTreeMap::new();
        for entry in std::fs::read_dir(path).expect("read_dir failed") {
            let entry = entry.expect("entry failed");
            let name = entry.file_name().to_string_lossy().to_string();
            entries.insert(name, read_fs_tree_recursively(&entry.path()));
        }
        FileSystemTree::Directory(entries)
    } else {
        FileSystemTree::File(Vec::new())
    }
}
