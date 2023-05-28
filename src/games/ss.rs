use std::net::IpAddr;
use crate::protocols::gamespy;
use crate::protocols::gamespy::one::Response;
use crate::GDResult;

pub fn query(address: &IpAddr, port: Option<u16>) -> GDResult<Response> {
    gamespy::one::query(address, port.unwrap_or(25601), None)
}
