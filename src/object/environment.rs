use crate::object::object::Object;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
    store: HashMap<String, Object>,
    outer: Option<Box<Env>>,
}

impl Env {
    pub fn new() -> Self {
        let store = HashMap::new();
        let outer = None;
        Self { store, outer }
    }

    pub fn new_enclosed_env(outer: Box<Env>) -> Self {
        let mut env = Self::new();
        env.outer = Some(outer);
        env
    }

    pub fn get(&self, key: &String) -> Option<Object> {
        if self.store.contains_key(key) {
            self.store.get(key).map(|obj| obj.clone())
        } else {
            self.outer.as_ref().and_then(|env| env.get(key))
        }
    }

    pub fn set(&mut self, key: impl Into<String>, obj: Object) -> Option<Object> {
        self.store.insert(key.into(), obj)
    }
}
