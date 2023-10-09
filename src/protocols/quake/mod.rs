#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod one;
pub mod three;
pub mod two;

/// All types used by the implementation.
pub mod types;
pub use types::*;

mod client;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuakeVersion {
    One,
    Two,
    Three,
}

/// Generate a module containing a query function for a quake game.
macro_rules! game_query_mod {
    ($mod_name: ident, $pretty_name: expr, $quake_ver: ident, $default_port: literal) => {
        #[doc = $pretty_name]
        pub mod $mod_name {
            crate::protocols::quake::game_query_fn!($quake_ver, $default_port);
        }
    };
}

pub(crate) use game_query_mod;

// Allow generating doc comments:
// https://users.rust-lang.org/t/macros-filling-text-in-comments/20473
/// Generate a query function for a quake game.
macro_rules! game_query_fn {
    ($quake_ver: ident, $default_port: literal) => {
        use crate::protocols::quake::$quake_ver::Player;
        crate::protocols::quake::game_query_fn! {@gen $quake_ver, Player, $default_port, concat!(
        "Make a quake ", stringify!($quake_ver), " query with default timeout settings.\n\n",
        "If port is `None`, then the default port (", stringify!($default_port), ") will be used.")}
    };

    (@gen $quake_ver: ident, $player_type: ty, $default_port: literal, $doc: expr) => {
        #[doc = $doc]
        pub fn query(
            address: &std::net::IpAddr,
            port: Option<u16>,
        ) -> crate::GDResult<crate::protocols::quake::Response<$player_type>> {
            crate::protocols::quake::$quake_ver::query(
                &std::net::SocketAddr::new(*address, port.unwrap_or($default_port)),
                None,
            )
        }
    };
}

pub(crate) use game_query_fn;
