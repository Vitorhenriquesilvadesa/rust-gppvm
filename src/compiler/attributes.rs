use std::collections::HashMap;

use crate::gpp_error;

use super::semantics::TypeDescriptor;

#[derive(Clone)]
pub struct Attribute {
    pub args: Vec<String>,
}

impl Attribute {
    pub fn new(args: Vec<String>) -> Self {
        Self { args }
    }
}

pub struct DefaultAttributes {
    pub attributes: HashMap<String, Attribute>,
}

impl DefaultAttributes {
    pub fn get() -> Self {
        Self {
            attributes: Self::register_attributes(),
        }
    }

    pub fn get_attribute(&self, name: String) -> &Attribute {
        self.attributes
            .get(&name)
            .or_else(|| {
                gpp_error!("Not registered attribute '{}'.", name);
            })
            .unwrap()
    }

    fn register_attributes() -> HashMap<String, Attribute> {
        let mut attribs: HashMap<String, Attribute> = HashMap::new();

        attribs.insert(
            "parallel".to_string(),
            Attribute::new(vec!["str".to_string()]),
        );

        attribs.insert(
            "num_threads".to_string(),
            Attribute::new(vec![
                "int".to_string(),
                "int".to_string(),
                "int".to_string(),
            ]),
        );

        attribs
    }
}
