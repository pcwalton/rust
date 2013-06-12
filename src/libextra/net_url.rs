// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Types/fns concerning URLs (see RFC 3986)

#[allow(missing_doc)];

use core::prelude::*;

use core::iterator::IteratorUtil;
use core::cmp::Eq;
use core::io::{Reader, ReaderUtil};
use core::io;
use core::hashmap::HashMap;
use core::to_bytes;
use core::uint;

#[deriving(Clone, Eq)]
struct Url {
    scheme: ~str,
    user: Option<UserInfo>,
    host: ~str,
    port: Option<~str>,
    path: ~str,
    query: Query,
    fragment: Option<~str>
}

#[deriving(Clone, Eq)]
struct UserInfo {
    user: ~str,
    pass: Option<~str>
}

pub type Query = ~[(~str, ~str)];

impl Url {
    pub fn new(scheme: ~str,
               user: Option<UserInfo>,
               host: ~str,
               port: Option<~str>,
               path: ~str,
               query: Query,
               fragment: Option<~str>)
               -> Url {
        Url {
            scheme: scheme,
            user: user,
            host: host,
            port: port,
            path: path,
            query: query,
            fragment: fragment,
        }
    }
}

impl UserInfo {
    pub fn new(user: ~str, pass: Option<~str>) -> UserInfo {
        UserInfo { user: user, pass: pass }
    }
}

fn encode_inner(s: &str, full_url: bool) -> ~str {
    do io::with_str_reader(s) |rdr| {
        let mut out = ~"";

        while !rdr.eof() {
            let ch = rdr.read_byte() as char;
            match ch {
              // unreserved:
              'A' .. 'Z' |
              'a' .. 'z' |
              '0' .. '9' |
              '-' | '.' | '_' | '~' => {
                out.push_char(ch);
              }
              _ => {
                  if full_url {
                    match ch {
                      // gen-delims:
                      ':' | '/' | '?' | '#' | '[' | ']' | '@' |

                      // sub-delims:
                      '!' | '$' | '&' | '"' | '(' | ')' | '*' |
                      '+' | ',' | ';' | '=' => {
                        out.push_char(ch);
                      }

                      _ => out.push_str(fmt!("%%%X", ch as uint))
                    }
                } else {
                    out.push_str(fmt!("%%%X", ch as uint));
                }
              }
            }
        }

        out
    }
}

/**
 * Encodes a URI by replacing reserved characters with percent encoded
 * character sequences.
 *
 * This function is compliant with RFC 3986.
 */
pub fn encode(s: &str) -> ~str {
    encode_inner(s, true)
}

/**
 * Encodes a URI component by replacing reserved characters with percent
 * encoded character sequences.
 *
 * This function is compliant with RFC 3986.
 */

pub fn encode_component(s: &str) -> ~str {
    encode_inner(s, false)
}

fn decode_inner(s: &str, full_url: bool) -> ~str {
    do io::with_str_reader(s) |rdr| {
        let mut out = ~"";

        while !rdr.eof() {
            match rdr.read_char() {
              '%' => {
                let bytes = rdr.read_bytes(2u);
                let ch = uint::parse_bytes(bytes, 16u).get() as char;

                if full_url {
                    // Only decode some characters:
                    match ch {
                      // gen-delims:
                      ':' | '/' | '?' | '#' | '[' | ']' | '@' |

                      // sub-delims:
                      '!' | '$' | '&' | '"' | '(' | ')' | '*' |
                      '+' | ',' | ';' | '=' => {
                        out.push_char('%');
                        out.push_char(bytes[0u] as char);
                        out.push_char(bytes[1u] as char);
                      }

                      ch => out.push_char(ch)
                    }
                } else {
                      out.push_char(ch);
                }
              }
              ch => out.push_char(ch)
            }
        }

        out
    }
}

/**
 * Decode a string encoded with percent encoding.
 *
 * This will only decode escape sequences generated by encode.
 */
pub fn decode(s: &str) -> ~str {
    decode_inner(s, true)
}

/**
 * Decode a string encoded with percent encoding.
 */
pub fn decode_component(s: &str) -> ~str {
    decode_inner(s, false)
}

fn encode_plus(s: &str) -> ~str {
    do io::with_str_reader(s) |rdr| {
        let mut out = ~"";

        while !rdr.eof() {
            let ch = rdr.read_byte() as char;
            match ch {
              'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '.' | '-' => {
                out.push_char(ch);
              }
              ' ' => out.push_char('+'),
              _ => out.push_str(fmt!("%%%X", ch as uint))
            }
        }

        out
    }
}

/**
 * Encode a hashmap to the 'application/x-www-form-urlencoded' media type.
 */
pub fn encode_form_urlencoded(m: &HashMap<~str, ~[~str]>) -> ~str {
    let mut out = ~"";
    let mut first = true;

    for m.each |key, values| {
        let key = encode_plus(*key);

        for values.each |value| {
            if first {
                first = false;
            } else {
                out.push_char('&');
                first = false;
            }

            out.push_str(fmt!("%s=%s", key, encode_plus(*value)));
        }
    }

    out
}

/**
 * Decode a string encoded with the 'application/x-www-form-urlencoded' media
 * type into a hashmap.
 */
pub fn decode_form_urlencoded(s: &[u8]) -> HashMap<~str, ~[~str]> {
    do io::with_bytes_reader(s) |rdr| {
        let mut m = HashMap::new();
        let mut key = ~"";
        let mut value = ~"";
        let mut parsing_key = true;

        while !rdr.eof() {
            match rdr.read_char() {
                '&' | ';' => {
                    if key != ~"" && value != ~"" {
                        let mut values = match m.pop(&key) {
                            Some(values) => values,
                            None => ~[],
                        };

                        values.push(value);
                        m.insert(key, values);
                    }

                    parsing_key = true;
                    key = ~"";
                    value = ~"";
                }
                '=' => parsing_key = false,
                ch => {
                    let ch = match ch {
                        '%' => {
                            let bytes = rdr.read_bytes(2u);
                            uint::parse_bytes(bytes, 16u).get() as char
                        }
                        '+' => ' ',
                        ch => ch
                    };

                    if parsing_key {
                        key.push_char(ch)
                    } else {
                        value.push_char(ch)
                    }
                }
            }
        }

        if key != ~"" && value != ~"" {
            let mut values = match m.pop(&key) {
                Some(values) => values,
                None => ~[],
            };

            values.push(value);
            m.insert(key, values);
        }

        m
    }
}


fn split_char_first(s: &str, c: char) -> (~str, ~str) {
    let len = s.len();
    let mut index = len;
    let mut mat = 0;
    do io::with_str_reader(s) |rdr| {
        let mut ch;
        while !rdr.eof() {
            ch = rdr.read_byte() as char;
            if ch == c {
                // found a match, adjust markers
                index = rdr.tell()-1;
                mat = 1;
                break;
            }
        }
    }
    if index+mat == len {
        return (s.slice(0, index).to_owned(), ~"");
    } else {
        return (s.slice(0, index).to_owned(),
             s.slice(index + mat, s.len()).to_owned());
    }
}

fn userinfo_from_str(uinfo: &str) -> UserInfo {
    let (user, p) = split_char_first(uinfo, ':');
    let pass = if p.is_empty() {
        None
    } else {
        Some(p)
    };
    return UserInfo::new(user, pass);
}

fn userinfo_to_str(userinfo: &UserInfo) -> ~str {
    match userinfo.pass {
        Some(ref pass) => fmt!("%s:%s@", userinfo.user, *pass),
        None => fmt!("%s@", userinfo.user),
    }
}

fn query_from_str(rawquery: &str) -> Query {
    let mut query: Query = ~[];
    if !rawquery.is_empty() {
        for rawquery.split_iter('&').advance |p| {
            let (k, v) = split_char_first(p, '=');
            query.push((decode_component(k), decode_component(v)));
        };
    }
    return query;
}

pub fn query_to_str(query: &Query) -> ~str {
    let mut strvec = ~[];
    for query.each |kv| {
        match kv {
            &(ref k, ref v) => {
                strvec.push(fmt!("%s=%s",
                    encode_component(*k),
                    encode_component(*v))
                );
            }
        }
    }
    return strvec.connect("&");
}

// returns the scheme and the rest of the url, or a parsing error
pub fn get_scheme(rawurl: &str) -> Result<(~str, ~str), ~str> {
    for rawurl.iter().enumerate().advance |(i,c)| {
        match c {
          'A' .. 'Z' | 'a' .. 'z' => loop,
          '0' .. '9' | '+' | '-' | '.' => {
            if i == 0 {
                return Err(~"url: Scheme must begin with a letter.");
            }
            loop;
          }
          ':' => {
            if i == 0 {
                return Err(~"url: Scheme cannot be empty.");
            } else {
                return Ok((rawurl.slice(0,i).to_owned(),
                                rawurl.slice(i+1,rawurl.len()).to_owned()));
            }
          }
          _ => {
            return Err(~"url: Invalid character in scheme.");
          }
        }
    };
    return Err(~"url: Scheme must be terminated with a colon.");
}

#[deriving(Clone, Eq)]
enum Input {
    Digit, // all digits
    Hex, // digits and letters a-f
    Unreserved // all other legal characters
}

// returns userinfo, host, port, and unparsed part, or an error
fn get_authority(rawurl: &str) ->
    Result<(Option<UserInfo>, ~str, Option<~str>, ~str), ~str> {
    if !rawurl.starts_with("//") {
        // there is no authority.
        return Ok((None, ~"", None, rawurl.to_str()));
    }

    enum State {
        Start, // starting state
        PassHostPort, // could be in user or port
        Ip6Port, // either in ipv6 host or port
        Ip6Host, // are in an ipv6 host
        InHost, // are in a host - may be ipv6, but don't know yet
        InPort // are in port
    }

    let len = rawurl.len();
    let mut st = Start;
    let mut in = Digit; // most restricted, start here.

    let mut userinfo = None;
    let mut host = ~"";
    let mut port = None;

    let mut colon_count = 0;
    let mut pos = 0;
    let mut begin = 2;
    let mut end = len;

    for rawurl.iter().enumerate().advance |(i,c)| {
        if i < 2 { loop; } // ignore the leading //

        // deal with input class first
        match c {
          '0' .. '9' => (),
          'A' .. 'F' | 'a' .. 'f' => {
            if in == Digit {
                in = Hex;
            }
          }
          'G' .. 'Z' | 'g' .. 'z' | '-' | '.' | '_' | '~' | '%' |
          '&' |'\'' | '(' | ')' | '+' | '!' | '*' | ',' | ';' | '=' => {
            in = Unreserved;
          }
          ':' | '@' | '?' | '#' | '/' => {
            // separators, don't change anything
          }
          _ => {
            return Err(~"Illegal character in authority");
          }
        }

        // now process states
        match c {
          ':' => {
            colon_count += 1;
            match st {
              Start => {
                pos = i;
                st = PassHostPort;
              }
              PassHostPort => {
                // multiple colons means ipv6 address.
                if in == Unreserved {
                    return Err(
                        ~"Illegal characters in IPv6 address.");
                }
                st = Ip6Host;
              }
              InHost => {
                pos = i;
                // can't be sure whether this is an ipv6 address or a port
                if in == Unreserved {
                    return Err(~"Illegal characters in authority.");
                }
                st = Ip6Port;
              }
              Ip6Port => {
                if in == Unreserved {
                    return Err(~"Illegal characters in authority.");
                }
                st = Ip6Host;
              }
              Ip6Host => {
                if colon_count > 7 {
                    host = rawurl.slice(begin, i).to_owned();
                    pos = i;
                    st = InPort;
                }
              }
              _ => {
                return Err(~"Invalid ':' in authority.");
              }
            }
            in = Digit; // reset input class
          }

          '@' => {
            in = Digit; // reset input class
            colon_count = 0; // reset count
            match st {
              Start => {
                let user = rawurl.slice(begin, i).to_owned();
                userinfo = Some(UserInfo::new(user, None));
                st = InHost;
              }
              PassHostPort => {
                let user = rawurl.slice(begin, pos).to_owned();
                let pass = rawurl.slice(pos+1, i).to_owned();
                userinfo = Some(UserInfo::new(user, Some(pass)));
                st = InHost;
              }
              _ => {
                return Err(~"Invalid '@' in authority.");
              }
            }
            begin = i+1;
          }

          '?' | '#' | '/' => {
            end = i;
            break;
          }
          _ => ()
        }
        end = i;
    }

    let end = end; // make end immutable so it can be captured

    let host_is_end_plus_one: &fn() -> bool = || {
        end+1 == len
            && !['?', '#', '/'].contains(&(rawurl[end] as char))
    };

    // finish up
    match st {
      Start => {
        if host_is_end_plus_one() {
            host = rawurl.slice(begin, end+1).to_owned();
        } else {
            host = rawurl.slice(begin, end).to_owned();
        }
      }
      PassHostPort | Ip6Port => {
        if in != Digit {
            return Err(~"Non-digit characters in port.");
        }
        host = rawurl.slice(begin, pos).to_owned();
        port = Some(rawurl.slice(pos+1, end).to_owned());
      }
      Ip6Host | InHost => {
        host = rawurl.slice(begin, end).to_owned();
      }
      InPort => {
        if in != Digit {
            return Err(~"Non-digit characters in port.");
        }
        port = Some(rawurl.slice(pos+1, end).to_owned());
      }
    }

    let rest = if host_is_end_plus_one() { ~"" }
    else { rawurl.slice(end, len).to_owned() };
    return Ok((userinfo, host, port, rest));
}


// returns the path and unparsed part of url, or an error
fn get_path(rawurl: &str, authority: bool) ->
    Result<(~str, ~str), ~str> {
    let len = rawurl.len();
    let mut end = len;
    for rawurl.iter().enumerate().advance |(i,c)| {
        match c {
          'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '&' |'\'' | '(' | ')' | '.'
          | '@' | ':' | '%' | '/' | '+' | '!' | '*' | ',' | ';' | '='
          | '_' | '-' => {
            loop;
          }
          '?' | '#' => {
            end = i;
            break;
          }
          _ => return Err(~"Invalid character in path.")
        }
    }

    if authority {
        if end != 0 && !rawurl.starts_with("/") {
            return Err(~"Non-empty path must begin with\
                               '/' in presence of authority.");
        }
    }

    return Ok((decode_component(rawurl.slice(0, end)),
                    rawurl.slice(end, len).to_owned()));
}

// returns the parsed query and the fragment, if present
fn get_query_fragment(rawurl: &str) ->
    Result<(Query, Option<~str>), ~str> {
    if !rawurl.starts_with("?") {
        if rawurl.starts_with("#") {
            let f = decode_component(rawurl.slice(
                                                1,
                                                rawurl.len()));
            return Ok((~[], Some(f)));
        } else {
            return Ok((~[], None));
        }
    }
    let (q, r) = split_char_first(rawurl.slice(1, rawurl.len()), '#');
    let f = if r.len() != 0 {
        Some(decode_component(r)) } else { None };
    return Ok((query_from_str(q), f));
}

/**
 * Parse a `str` to a `url`
 *
 * # Arguments
 *
 * `rawurl` - a string representing a full url, including scheme.
 *
 * # Returns
 *
 * a `url` that contains the parsed representation of the url.
 *
 */

pub fn from_str(rawurl: &str) -> Result<Url, ~str> {
    // scheme
    let (scheme, rest) = match get_scheme(rawurl) {
        Ok(val) => val,
        Err(e) => return Err(e),
    };

    // authority
    let (userinfo, host, port, rest) = match get_authority(rest) {
        Ok(val) => val,
        Err(e) => return Err(e),
    };

    // path
    let has_authority = if host == ~"" { false } else { true };
    let (path, rest) = match get_path(rest, has_authority) {
        Ok(val) => val,
        Err(e) => return Err(e),
    };

    // query and fragment
    let (query, fragment) = match get_query_fragment(rest) {
        Ok(val) => val,
        Err(e) => return Err(e),
    };

    Ok(Url::new(scheme, userinfo, host, port, path, query, fragment))
}

impl FromStr for Url {
    fn from_str(s: &str) -> Option<Url> {
        match from_str(s) {
            Ok(url) => Some(url),
            Err(_) => None
        }
    }
}

/**
 * Format a `url` as a string
 *
 * # Arguments
 *
 * `url` - a url.
 *
 * # Returns
 *
 * a `str` that contains the formatted url. Note that this will usually
 * be an inverse of `from_str` but might strip out unneeded separators.
 * for example, "http://somehost.com?", when parsed and formatted, will
 * result in just "http://somehost.com".
 *
 */
pub fn to_str(url: &Url) -> ~str {
    let user = match url.user {
        Some(ref user) => userinfo_to_str(user),
        None => ~"",
    };

    let authority = if url.host.is_empty() {
        ~""
    } else {
        fmt!("//%s%s", user, url.host)
    };

    let query = if url.query.is_empty() {
        ~""
    } else {
        fmt!("?%s", query_to_str(&url.query))
    };

    let fragment = match url.fragment {
        Some(ref fragment) => fmt!("#%s", encode_component(*fragment)),
        None => ~"",
    };

    fmt!("%s:%s%s%s%s", url.scheme, authority, url.path, query, fragment)
}

impl ToStr for Url {
    pub fn to_str(&self) -> ~str {
        to_str(self)
    }
}

impl IterBytes for Url {
    fn iter_bytes(&self, lsb0: bool, f: to_bytes::Cb) -> bool {
        self.to_str().iter_bytes(lsb0, f)
    }
}

// Put a few tests outside of the 'test' module so they can test the internal
// functions and those functions don't need 'pub'

#[test]
fn test_split_char_first() {
    let (u,v) = split_char_first("hello, sweet world", ',');
    assert_eq!(u, ~"hello");
    assert_eq!(v, ~" sweet world");

    let (u,v) = split_char_first("hello sweet world", ',');
    assert_eq!(u, ~"hello sweet world");
    assert_eq!(v, ~"");
}

#[test]
fn test_get_authority() {
    let (u, h, p, r) = get_authority(
        "//user:pass@rust-lang.org/something").unwrap();
    assert_eq!(u, Some(UserInfo::new(~"user", Some(~"pass"))));
    assert_eq!(h, ~"rust-lang.org");
    assert!(p.is_none());
    assert_eq!(r, ~"/something");

    let (u, h, p, r) = get_authority(
        "//rust-lang.org:8000?something").unwrap();
    assert!(u.is_none());
    assert_eq!(h, ~"rust-lang.org");
    assert_eq!(p, Some(~"8000"));
    assert_eq!(r, ~"?something");

    let (u, h, p, r) = get_authority(
        "//rust-lang.org#blah").unwrap();
    assert!(u.is_none());
    assert_eq!(h, ~"rust-lang.org");
    assert!(p.is_none());
    assert_eq!(r, ~"#blah");

    // ipv6 tests
    let (_, h, _, _) = get_authority(
        "//2001:0db8:85a3:0042:0000:8a2e:0370:7334#blah").unwrap();
    assert_eq!(h, ~"2001:0db8:85a3:0042:0000:8a2e:0370:7334");

    let (_, h, p, _) = get_authority(
        "//2001:0db8:85a3:0042:0000:8a2e:0370:7334:8000#blah").unwrap();
    assert_eq!(h, ~"2001:0db8:85a3:0042:0000:8a2e:0370:7334");
    assert_eq!(p, Some(~"8000"));

    let (u, h, p, _) = get_authority(
        "//us:p@2001:0db8:85a3:0042:0000:8a2e:0370:7334:8000#blah"
    ).unwrap();
    assert_eq!(u, Some(UserInfo::new(~"us", Some(~"p"))));
    assert_eq!(h, ~"2001:0db8:85a3:0042:0000:8a2e:0370:7334");
    assert_eq!(p, Some(~"8000"));

    // invalid authorities;
    assert!(get_authority("//user:pass@rust-lang:something").is_err());
    assert!(get_authority("//user@rust-lang:something:/path").is_err());
    assert!(get_authority(
        "//2001:0db8:85a3:0042:0000:8a2e:0370:7334:800a").is_err());
    assert!(get_authority(
        "//2001:0db8:85a3:0042:0000:8a2e:0370:7334:8000:00").is_err());

    // these parse as empty, because they don't start with '//'
    let (_, h, _, _) = get_authority("user:pass@rust-lang").unwrap();
    assert_eq!(h, ~"");
    let (_, h, _, _) = get_authority("rust-lang.org").unwrap();
    assert_eq!(h, ~"");
}

#[test]
fn test_get_path() {
    let (p, r) = get_path("/something+%20orother", true).unwrap();
    assert_eq!(p, ~"/something+ orother");
    assert_eq!(r, ~"");
    let (p, r) = get_path("test@email.com#fragment", false).unwrap();
    assert_eq!(p, ~"test@email.com");
    assert_eq!(r, ~"#fragment");
    let (p, r) = get_path("/gen/:addr=?q=v", false).unwrap();
    assert_eq!(p, ~"/gen/:addr=");
    assert_eq!(r, ~"?q=v");

    //failure cases
    assert!(get_path("something?q", true).is_err());
}

#[cfg(test)]
mod tests {

    use net_url::*;

    use core::hashmap::HashMap;

    #[test]
    fn test_url_parse() {
        let url = ~"http://user:pass@rust-lang.org/doc?s=v#something";

        let up = from_str(url);
        let u = up.unwrap();
        assert!(u.scheme == ~"http");
        let userinfo = u.user.get_ref();
        assert!(userinfo.user == ~"user");
        assert!(userinfo.pass.get_ref() == &~"pass");
        assert!(u.host == ~"rust-lang.org");
        assert!(u.path == ~"/doc");
        assert!(u.query == ~[(~"s", ~"v")]);
        assert!(u.fragment.get_ref() == &~"something");
    }

    #[test]
    fn test_url_parse_host_slash() {
        let urlstr = ~"http://0.42.42.42/";
        let url = from_str(urlstr).unwrap();
        assert!(url.host == ~"0.42.42.42");
        assert!(url.path == ~"/");
    }

    #[test]
    fn test_url_with_underscores() {
        let urlstr = ~"http://dotcom.com/file_name.html";
        let url = from_str(urlstr).unwrap();
        assert!(url.path == ~"/file_name.html");
    }

    #[test]
    fn test_url_with_dashes() {
        let urlstr = ~"http://dotcom.com/file-name.html";
        let url = from_str(urlstr).unwrap();
        assert!(url.path == ~"/file-name.html");
    }

    #[test]
    fn test_no_scheme() {
        assert!(get_scheme("noschemehere.html").is_err());
    }

    #[test]
    fn test_invalid_scheme_errors() {
        assert!(from_str("99://something").is_err());
        assert!(from_str("://something").is_err());
    }

    #[test]
    fn test_full_url_parse_and_format() {
        let url = ~"http://user:pass@rust-lang.org/doc?s=v#something";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_userless_url_parse_and_format() {
        let url = ~"http://rust-lang.org/doc?s=v#something";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_queryless_url_parse_and_format() {
        let url = ~"http://user:pass@rust-lang.org/doc#something";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_empty_query_url_parse_and_format() {
        let url = ~"http://user:pass@rust-lang.org/doc?#something";
        let should_be = ~"http://user:pass@rust-lang.org/doc#something";
        assert_eq!(from_str(url).unwrap().to_str(), should_be);
    }

    #[test]
    fn test_fragmentless_url_parse_and_format() {
        let url = ~"http://user:pass@rust-lang.org/doc?q=v";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_minimal_url_parse_and_format() {
        let url = ~"http://rust-lang.org/doc";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_scheme_host_only_url_parse_and_format() {
        let url = ~"http://rust-lang.org";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_pathless_url_parse_and_format() {
        let url = ~"http://user:pass@rust-lang.org?q=v#something";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_scheme_host_fragment_only_url_parse_and_format() {
        let url = ~"http://rust-lang.org#something";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_url_component_encoding() {
        let url = ~"http://rust-lang.org/doc%20uments?ba%25d%20=%23%26%2B";
        let u = from_str(url).unwrap();
        assert!(u.path == ~"/doc uments");
        assert!(u.query == ~[(~"ba%d ", ~"#&+")]);
    }

    #[test]
    fn test_url_without_authority() {
        let url = ~"mailto:test@email.com";
        assert_eq!(from_str(url).unwrap().to_str(), url);
    }

    #[test]
    fn test_encode() {
        assert_eq!(encode(""), ~"");
        assert_eq!(encode("http://example.com"), ~"http://example.com");
        assert_eq!(encode("foo bar% baz"), ~"foo%20bar%25%20baz");
        assert_eq!(encode(" "), ~"%20");
        assert_eq!(encode("!"), ~"!");
        assert_eq!(encode("\""), ~"\"");
        assert_eq!(encode("#"), ~"#");
        assert_eq!(encode("$"), ~"$");
        assert_eq!(encode("%"), ~"%25");
        assert_eq!(encode("&"), ~"&");
        assert_eq!(encode("'"), ~"%27");
        assert_eq!(encode("("), ~"(");
        assert_eq!(encode(")"), ~")");
        assert_eq!(encode("*"), ~"*");
        assert_eq!(encode("+"), ~"+");
        assert_eq!(encode(","), ~",");
        assert_eq!(encode("/"), ~"/");
        assert_eq!(encode(":"), ~":");
        assert_eq!(encode(";"), ~";");
        assert_eq!(encode("="), ~"=");
        assert_eq!(encode("?"), ~"?");
        assert_eq!(encode("@"), ~"@");
        assert_eq!(encode("["), ~"[");
        assert_eq!(encode("]"), ~"]");
    }

    #[test]
    fn test_encode_component() {
        assert_eq!(encode_component(""), ~"");
        assert!(encode_component("http://example.com") ==
            ~"http%3A%2F%2Fexample.com");
        assert!(encode_component("foo bar% baz") ==
            ~"foo%20bar%25%20baz");
        assert_eq!(encode_component(" "), ~"%20");
        assert_eq!(encode_component("!"), ~"%21");
        assert_eq!(encode_component("#"), ~"%23");
        assert_eq!(encode_component("$"), ~"%24");
        assert_eq!(encode_component("%"), ~"%25");
        assert_eq!(encode_component("&"), ~"%26");
        assert_eq!(encode_component("'"), ~"%27");
        assert_eq!(encode_component("("), ~"%28");
        assert_eq!(encode_component(")"), ~"%29");
        assert_eq!(encode_component("*"), ~"%2A");
        assert_eq!(encode_component("+"), ~"%2B");
        assert_eq!(encode_component(","), ~"%2C");
        assert_eq!(encode_component("/"), ~"%2F");
        assert_eq!(encode_component(":"), ~"%3A");
        assert_eq!(encode_component(";"), ~"%3B");
        assert_eq!(encode_component("="), ~"%3D");
        assert_eq!(encode_component("?"), ~"%3F");
        assert_eq!(encode_component("@"), ~"%40");
        assert_eq!(encode_component("["), ~"%5B");
        assert_eq!(encode_component("]"), ~"%5D");
    }

    #[test]
    fn test_decode() {
        assert_eq!(decode(""), ~"");
        assert_eq!(decode("abc/def 123"), ~"abc/def 123");
        assert_eq!(decode("abc%2Fdef%20123"), ~"abc%2Fdef 123");
        assert_eq!(decode("%20"), ~" ");
        assert_eq!(decode("%21"), ~"%21");
        assert_eq!(decode("%22"), ~"%22");
        assert_eq!(decode("%23"), ~"%23");
        assert_eq!(decode("%24"), ~"%24");
        assert_eq!(decode("%25"), ~"%");
        assert_eq!(decode("%26"), ~"%26");
        assert_eq!(decode("%27"), ~"'");
        assert_eq!(decode("%28"), ~"%28");
        assert_eq!(decode("%29"), ~"%29");
        assert_eq!(decode("%2A"), ~"%2A");
        assert_eq!(decode("%2B"), ~"%2B");
        assert_eq!(decode("%2C"), ~"%2C");
        assert_eq!(decode("%2F"), ~"%2F");
        assert_eq!(decode("%3A"), ~"%3A");
        assert_eq!(decode("%3B"), ~"%3B");
        assert_eq!(decode("%3D"), ~"%3D");
        assert_eq!(decode("%3F"), ~"%3F");
        assert_eq!(decode("%40"), ~"%40");
        assert_eq!(decode("%5B"), ~"%5B");
        assert_eq!(decode("%5D"), ~"%5D");
    }

    #[test]
    fn test_decode_component() {
        assert_eq!(decode_component(""), ~"");
        assert_eq!(decode_component("abc/def 123"), ~"abc/def 123");
        assert_eq!(decode_component("abc%2Fdef%20123"), ~"abc/def 123");
        assert_eq!(decode_component("%20"), ~" ");
        assert_eq!(decode_component("%21"), ~"!");
        assert_eq!(decode_component("%22"), ~"\"");
        assert_eq!(decode_component("%23"), ~"#");
        assert_eq!(decode_component("%24"), ~"$");
        assert_eq!(decode_component("%25"), ~"%");
        assert_eq!(decode_component("%26"), ~"&");
        assert_eq!(decode_component("%27"), ~"'");
        assert_eq!(decode_component("%28"), ~"(");
        assert_eq!(decode_component("%29"), ~")");
        assert_eq!(decode_component("%2A"), ~"*");
        assert_eq!(decode_component("%2B"), ~"+");
        assert_eq!(decode_component("%2C"), ~",");
        assert_eq!(decode_component("%2F"), ~"/");
        assert_eq!(decode_component("%3A"), ~":");
        assert_eq!(decode_component("%3B"), ~";");
        assert_eq!(decode_component("%3D"), ~"=");
        assert_eq!(decode_component("%3F"), ~"?");
        assert_eq!(decode_component("%40"), ~"@");
        assert_eq!(decode_component("%5B"), ~"[");
        assert_eq!(decode_component("%5D"), ~"]");
    }

    #[test]
    fn test_encode_form_urlencoded() {
        let mut m = HashMap::new();
        assert_eq!(encode_form_urlencoded(&m), ~"");

        m.insert(~"", ~[]);
        m.insert(~"foo", ~[]);
        assert_eq!(encode_form_urlencoded(&m), ~"");

        let mut m = HashMap::new();
        m.insert(~"foo", ~[~"bar", ~"123"]);
        assert_eq!(encode_form_urlencoded(&m), ~"foo=bar&foo=123");

        let mut m = HashMap::new();
        m.insert(~"foo bar", ~[~"abc", ~"12 = 34"]);
        assert!(encode_form_urlencoded(&m) ==
            ~"foo+bar=abc&foo+bar=12+%3D+34");
    }

    #[test]
    fn test_decode_form_urlencoded() {
        // FIXME #4449: Commented out because this causes an ICE, but only
        // on FreeBSD
        /*
        assert_eq!(decode_form_urlencoded([]).len(), 0);

        let s = str::to_bytes("a=1&foo+bar=abc&foo+bar=12+%3D+34");
        let form = decode_form_urlencoded(s);
        assert_eq!(form.len(), 2);
        assert_eq!(form.get_ref(&~"a"), &~[~"1"]);
        assert_eq!(form.get_ref(&~"foo bar"), &~[~"abc", ~"12 = 34"]);
        */
    }
}
