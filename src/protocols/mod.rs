//! Protocols that are currently implemented.
//!
//! A protocol will be here if it supports multiple entries, if not, its
//! implementation will be in that specific needed place, a protocol can be
//! independently queried.

#[cfg(feature = "serde")]
use serde::{Serialize,Deserialize};

/// Reference: [node-GameDig](https://github.com/gamedig/node-gamedig/blob/master/protocols/gamespy1.js)
pub mod gamespy;
/// Reference: [Server List Ping](https://wiki.vg/Server_List_Ping)
pub mod minecraft;
/// Reference: [node-GameDig](https://github.com/gamedig/node-gamedig/blob/master/protocols/quake1.js)
pub mod quake;
/// General types that are used by all protocols.
pub mod types;
/// Reference: [Server Query](https://developer.valvesoftware.com/wiki/Server_queries)
pub mod valve;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq)]
pub enum Protocol {
    Gamespy(gamespy::GameSpyVersion),
    Minecraft(Option<minecraft::MinecraftVersion>),
    Quake(quake::QuakeVersion),
    Valve(valve::SteamApp),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq)]
pub struct GenericResponse {
    pub server_name: Option<String>,
    pub server_description: Option<String>,
    pub server_game: Option<String>,
    pub server_game_version: Option<String>,
    pub server_map: Option<String>,
    pub players_maximum: Option<u64>,
    pub players_online: Option<u64>,
    pub players_bots: Option<u64>,
    pub has_password: Option<bool>,
    // TODO: Add players (+rules?)
    pub inner: SpecificResponse,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq)]
pub enum SpecificResponse {
    Gamespy(gamespy::ResponseVersion),
    Minecraft(minecraft::JavaResponse),
    Quake(quake::Response<()>),
    Valve(valve::Response),
}
