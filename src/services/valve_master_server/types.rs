use std::collections::HashMap;
use std::mem::Discriminant;

/// A query filter.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Filter {
    IsSecured(bool),
    RunsMap(String),
    CanHavePassword(bool),
    CanBeEmpty(bool),
    IsEmpty(bool),
    CanBeFull(bool),
    RunsAppID(u32),
    NotAppID(u32),
    HasTags(Vec<String>),
    MatchName(String),
    MatchVersion(String),
    /// Restrict to only a server if an IP hosts (on different ports) multiple servers.
    RestrictUniqueIP(bool),
    /// Query for servers on a specific address.
    OnAddress(String),
    Whitelisted(bool),
    SpectatorProxy(bool),
    IsDedicated(bool),
    RunsLinux(bool),
    HasGameDir(String),
}

fn bool_as_char_u8(b: &bool) -> u8 {
    match b {
        true => b'1',
        false => b'0',
    }
}

impl Filter {
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();

        match self {
            Filter::IsSecured(secured) => {
                bytes = "\\secure\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(secured)]);
            }
            Filter::RunsMap(map) => {
                bytes = "\\map\\".as_bytes().to_vec();
                bytes.extend(map.as_bytes());
            }
            Filter::CanHavePassword(password) => {
                bytes = "\\password\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(password)]);
            }
            Filter::CanBeEmpty(empty) => {
                bytes = "\\empty\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(empty)]);
            }
            Filter::CanBeFull(full) => {
                bytes = "\\full\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(full)]);
            }
            Filter::RunsAppID(id) => {
                bytes = "\\appid\\".as_bytes().to_vec();
                bytes.extend(id.to_string().as_bytes());
            }
            Filter::HasTags(tags) => {
                if !tags.is_empty() {
                    bytes = "\\gametype\\".as_bytes().to_vec();
                    for tag in tags.iter() {
                        bytes.extend(tag.as_bytes());
                        bytes.extend([b',']);
                    }

                    bytes.pop();
                }
            }
            Filter::NotAppID(id) => {
                bytes = "\\napp\\".as_bytes().to_vec();
                bytes.extend(id.to_string().as_bytes());
            }
            Filter::IsEmpty(empty) => {
                bytes = "\\noplayers\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(empty)]);
            }
            Filter::MatchName(name) => {
                bytes = "\\name_match\\".as_bytes().to_vec();
                bytes.extend(name.as_bytes());
            }
            Filter::MatchVersion(version) => {
                bytes = "\\version_match\\".as_bytes().to_vec();
                bytes.extend(version.as_bytes());
            }
            Filter::RestrictUniqueIP(unique) => {
                bytes = "\\collapse_addr_hash\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(unique)]);
            }
            Filter::OnAddress(address) => {
                bytes = "\\gameaddr\\".as_bytes().to_vec();
                bytes.extend(address.as_bytes());
            }
            Filter::Whitelisted(whitelisted) => {
                bytes = "\\white\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(whitelisted)]);
            }
            Filter::SpectatorProxy(condition) => {
                bytes = "\\proxy\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(condition)]);
            }
            Filter::IsDedicated(dedicated) => {
                bytes = "\\dedicated\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(dedicated)]);
            }
            Filter::RunsLinux(linux) => {
                bytes = "\\linux\\".as_bytes().to_vec();
                bytes.extend([bool_as_char_u8(linux)]);
            }
            Filter::HasGameDir(game_dir) => {
                bytes = "\\gamedir\\".as_bytes().to_vec();
                bytes.extend(game_dir.as_bytes());
            }
        }

        bytes
    }
}

/// Query search filters.
/// An example of constructing one:
/// ```rust
/// use gamedig::valve_master_server::{Filter, SearchFilters};
///
/// let search_filters = SearchFilters::new()
///             .insert(Filter::RunsAppID(440))
///             .insert(Filter::IsEmpty(false))
///             .insert(Filter::CanHavePassword(false));
/// ```
/// This will construct filters that search for servers that can't have a password, are not empty and run App ID 440.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SearchFilters {
    filters: HashMap<Discriminant<Filter>, Filter>,
    nor_filters: HashMap<Discriminant<Filter>, Filter>,
    nand_filters: HashMap<Discriminant<Filter>, Filter>,
}

impl Default for SearchFilters {
    fn default() -> Self { SearchFilters::new() }
}

impl SearchFilters {
    pub fn new() -> Self {
        Self {
            filters: HashMap::new(),
            nor_filters: HashMap::new(),
            nand_filters: HashMap::new(),
        }
    }

    pub fn insert(self, filter: Filter) -> Self {
        let mut updated_fitler = self.filters;
        updated_fitler.insert(std::mem::discriminant(&filter), filter);

        Self {
            filters: updated_fitler,
            nand_filters: self.nand_filters,
            nor_filters: self.nor_filters,
        }
    }

    pub fn insert_nand(self, filter: Filter) -> Self {
        let mut updated_fitler = self.nor_filters;
        updated_fitler.insert(std::mem::discriminant(&filter), filter);

        Self {
            filters: self.filters,
            nand_filters: self.nand_filters,
            nor_filters: updated_fitler,
        }
    }

    pub fn insert_nor(self, filter: Filter) -> Self {
        let mut updated_fitler = self.nand_filters;
        updated_fitler.insert(std::mem::discriminant(&filter), filter);

        Self {
            filters: self.filters,
            nand_filters: updated_fitler,
            nor_filters: self.nor_filters,
        }
    }

    fn special_filter_to_bytes(name: &str, filters: &HashMap<Discriminant<Filter>, Filter>) -> Vec<u8> {
        let mut bytes = Vec::new();

        if !filters.is_empty() {
            bytes.extend(name.as_bytes());
            bytes.extend(filters.len().to_string().as_bytes());
            for filter in filters.values() {
                bytes.extend(filter.to_bytes());
            }
        }

        bytes
    }

    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::new();

        for filter in self.filters.values() {
            bytes.extend(filter.to_bytes())
        }

        bytes.extend(SearchFilters::special_filter_to_bytes("nand", &self.nand_filters));
        bytes.extend(SearchFilters::special_filter_to_bytes("nor", &self.nor_filters));

        bytes.extend([0x00]);
        bytes
    }
}

/// The region that you want to query server for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum Region {
    UsEast = 0x00,
    UsWest = 0x01,
    AmericaSouth = 0x02,
    Europe = 0x03,
    Asia = 0x04,
    Australia = 0x05,
    MiddleEast = 0x06,
    Africa = 0x07,
    Others = 0xFF,
}
