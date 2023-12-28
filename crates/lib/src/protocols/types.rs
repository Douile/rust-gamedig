use crate::minecraft;
use crate::protocols::{gamespy, quake, unreal2, valve};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Enumeration of all custom protocols
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProprietaryProtocol {
    TheShip,
    Minecraft(Option<minecraft::types::Server>),
    FFOW,
    JC2M,
}

/// Enumeration of all valid protocol types
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Protocol {
    Gamespy(gamespy::GameSpyVersion),
    Quake(quake::QuakeVersion),
    Valve(valve::Engine),
    Unreal2,
    #[cfg(feature = "games")]
    PROPRIETARY(ProprietaryProtocol),
}

/// All response types
#[derive(Debug, Clone, PartialEq)]
pub enum GenericResponse<'a> {
    GameSpy(gamespy::VersionedResponse<'a>),
    Quake(quake::VersionedResponse<'a>),
    Valve(&'a valve::Response),
    Unreal2(&'a unreal2::Response),
    #[cfg(feature = "games")]
    Minecraft(minecraft::VersionedResponse<'a>),
    #[cfg(feature = "games")]
    TheShip(&'a crate::games::theship::Response),
    #[cfg(feature = "games")]
    FFOW(&'a crate::games::ffow::Response),
    #[cfg(feature = "games")]
    JC2M(&'a crate::games::jc2m::Response),
}

/// All player types
#[derive(Debug, Clone, PartialEq)]
pub enum GenericPlayer<'a> {
    Valve(&'a valve::ServerPlayer),
    QuakeOne(&'a quake::one::Player),
    QuakeTwo(&'a quake::two::Player),
    Gamespy(gamespy::VersionedPlayer<'a>),
    Unreal2(&'a unreal2::Player),
    #[cfg(feature = "games")]
    Minecraft(&'a minecraft::Player),
    #[cfg(feature = "games")]
    TheShip(&'a crate::games::theship::TheShipPlayer),
    #[cfg(feature = "games")]
    JCMP2(&'a crate::games::jc2m::Player),
}

pub trait CommonResponse {
    /// Get the original response type
    fn as_original(&self) -> GenericResponse;
    /// Get a struct that can be stored as JSON (you don't need to override
    /// this)
    fn as_json(&self) -> CommonResponseJson {
        CommonResponseJson {
            name: self.name(),
            description: self.description(),
            game_mode: self.game_mode(),
            game_version: self.game_version(),
            has_password: self.has_password(),
            map: self.map(),
            players_maximum: self.players_maximum(),
            players_online: self.players_online(),
            players_bots: self.players_bots(),
            players: self
                .players()
                .map(|players| players.iter().map(|p| p.as_json()).collect()),
        }
    }

    /// The name of the server
    fn name(&self) -> Option<&str> { None }
    /// Description of the server
    fn description(&self) -> Option<&str> { None }
    /// Name of the current game or game mode
    fn game_mode(&self) -> Option<&str> { None }
    /// Version of the game being run on the server
    fn game_version(&self) -> Option<&str> { None }
    /// The current map name
    fn map(&self) -> Option<&str> { None }
    /// Maximum number of players allowed to connect
    fn players_maximum(&self) -> u32;
    /// Number of players currently connected
    fn players_online(&self) -> u32;
    /// Number of bots currently connected
    fn players_bots(&self) -> Option<u32> { None }
    /// Whether the server requires a password to join
    fn has_password(&self) -> Option<bool> { None }
    /// Currently connected players
    fn players(&self) -> Option<Vec<&dyn CommonPlayer>> { None }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CommonResponseJson<'a> {
    pub name: Option<&'a str>,
    pub description: Option<&'a str>,
    pub game_mode: Option<&'a str>,
    pub game_version: Option<&'a str>,
    pub map: Option<&'a str>,
    pub players_maximum: u32,
    pub players_online: u32,
    pub players_bots: Option<u32>,
    pub has_password: Option<bool>,
    pub players: Option<Vec<CommonPlayerJson<'a>>>,
}

pub trait CommonPlayer {
    /// Get the original player type
    fn as_original(&self) -> GenericPlayer;
    /// Get a struct that can be stored as JSON (you don't need to override
    /// this)
    fn as_json(&self) -> CommonPlayerJson {
        CommonPlayerJson {
            name: self.name(),
            score: self.score(),
        }
    }

    /// Player name
    fn name(&self) -> &str;
    /// Player score
    fn score(&self) -> Option<i32> { None }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CommonPlayerJson<'a> {
    pub name: &'a str,
    pub score: Option<i32>,
}

/// Generic extra request settings
///
/// Fields of this struct may not be used depending on which protocol
/// is selected, the individual fields link to the specific places
/// they will be used with additional documentation.
///
/// ## Examples
/// Create minecraft settings with builder:
/// ```
/// use gamedig::games::minecraft;
/// use gamedig::protocols::ExtraRequestSettings;
/// let mc_settings: minecraft::RequestSettings = ExtraRequestSettings::default().set_hostname("mc.hypixel.net".to_string()).into();
/// ```
///
/// Create valve settings with builder:
/// ```
/// use gamedig::protocols::{valve, ExtraRequestSettings};
/// let valve_settings: valve::GatheringSettings = ExtraRequestSettings::default().set_check_app_id(false).into();
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ExtraRequestSettings {
    /// The server's hostname.
    ///
    /// Used by:
    /// - [minecraft::RequestSettings#structfield.hostname]
    pub hostname: Option<String>,
    /// The protocol version to use.
    ///
    /// Used by:
    /// - [minecraft::RequestSettings#structfield.protocol_version]
    pub protocol_version: Option<i32>,
    /// Whether to gather player information
    ///
    /// Used by:
    /// - [valve::GatheringSettings#structfield.players]
    pub gather_players: Option<bool>,
    /// Whether to gather rule information.
    ///
    /// Used by:
    /// - [valve::GatheringSettings#structfield.rules]
    pub gather_rules: Option<bool>,
    /// Whether to check if the App ID is valid.
    ///
    /// Used by:
    /// - [valve::GatheringSettings#structfield.check_app_id]
    pub check_app_id: Option<bool>,
}

impl ExtraRequestSettings {
    /// [Sets hostname](ExtraRequestSettings#structfield.hostname)
    pub fn set_hostname(mut self, hostname: String) -> Self {
        self.hostname = Some(hostname);
        self
    }
    /// [Sets protocol
    /// version](ExtraRequestSettings#structfield.protocol_version)
    pub fn set_protocol_version(mut self, protocol_version: i32) -> Self {
        self.protocol_version = Some(protocol_version);
        self
    }
    /// [Sets gather players](ExtraRequestSettings#structfield.gather_players)
    pub fn set_gather_players(mut self, gather_players: bool) -> Self {
        self.gather_players = Some(gather_players);
        self
    }
    /// [Sets gather rules](ExtraRequestSettings#structfield.gather_rules)
    pub fn set_gather_rules(mut self, gather_rules: bool) -> Self {
        self.gather_rules = Some(gather_rules);
        self
    }
    /// [Sets check app ID](ExtraRequestSettings#structfield.check_app_id)
    pub fn set_check_app_id(mut self, check_app_id: bool) -> Self {
        self.check_app_id = Some(check_app_id);
        self
    }
}

use crate::types::TimeoutSettings as NewTimeoutSettings;
#[deprecated(
    since = "0.5.0",
    note = "TimeoutSettings has been moved to gamedig::TimeoutSettings"
)]
pub type TimeoutSettings = NewTimeoutSettings;

#[cfg(test)]
mod tests {
    use super::*;

    // Test that extra request settings can be converted
    #[test]
    fn test_extra_request_settings() {
        let settings = ExtraRequestSettings::default();

        let _: valve::GatheringSettings = settings.into();
    }
}
