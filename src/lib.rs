// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{io, ptr, str, usize};
mod c {
    #![allow(non_snake_case)]
    pub type DWORD = u32;
    pub unsafe fn GetLastError() -> DWORD {
        unimplemented!()
    }
    pub unsafe fn SetLastError(_q: DWORD) {
        unimplemented!()
    }
    pub const ERROR_INSUFFICIENT_BUFFER: DWORD = 0;
    pub unsafe fn GetFullPathNameW<A>(_ptr: *const u16,
                                      _len: u32,
                                      _input: *mut u16,
                                      _file_part: *mut *const u16)
                                      -> A {
        unimplemented!()
    }
}
// True iff a u8 is a path separator
fn is_sep(q: u8) -> bool {
    match q {
        b'\\' | b'/' => true,
        _ => false,
    }
}

// The number of leading path separators
fn num_slashes<'a, T>(path: T) -> usize
    where T: IntoIterator<Item = &'a u8>
{
    let mut count = 0usize;
    for &i in path {
        if is_sep(i) && count < 3 {
            count += 1
        } else {
            return count;
        }
    }
    return count;
}

// Parse the first two components of a path
fn parse_two_comps(mut path: &[u8]) -> Option<(&[u8], &[u8])> {
    let first = match path.iter().position(|x| is_sep(*x)) {
        None => return None,
        Some(x) => &path[..x],
    };
    path = &path[(first.len() + 1)..];
    let idx = path.iter().position(|x| is_sep(*x));
    let second = &path[..idx.unwrap_or(path.len())];
    Some((first, second))
}

const SEP: u16 = b'\\' as u16;
fn do_special<T, U>(path: &[u8],
                    fst: usize,
                    snd: usize,
                    thrd: usize,
                    cb: T)
                    -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{
    let buf: Result<&str, BadPathError> = str::from_utf8(path).map_err(BadPathError::BadWTF8);
    let mut sixteen = do_convert_launch(buf?);
    sixteen[fst] = SEP;
    sixteen[snd] = SEP;
    sixteen[thrd] = SEP;
    Ok(cb(&mut sixteen))
}


// Run GetFullPathNameW
fn do_conv<T, U>(prefix: &[u16], buf: &[u16], cb: T) -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{
    fill_utf16_buf_with_prefix(prefix,
                               |ptr, len| unsafe {
                                   c::GetFullPathNameW(buf.as_ptr(), len, ptr, ptr::null_mut())
                               },
                               |x| {
                                   let l = x.len() - 2;
                                   cb(&mut x[..l])
                               })
        .map_err(BadPathError::IoError)
}

const VERB_PREFIX_16: [u16; 4] = [b'\\' as u16, b'\\' as u16, b'?' as u16, b'\\' as u16];
const UNC_PREFIX_16: [u16; 8] = [b'\\' as u16,
                                 b'\\' as u16,
                                 b'?' as u16,
                                 b'\\' as u16,
                                 b'U' as u16,
                                 b'N' as u16,
                                 b'C' as u16,
                                 b'\\' as u16];

fn do_convert_launch(buf: &str) -> Vec<u16> {
    UNC_PREFIX_16.iter().map(|&x| x).chain(buf[2..].encode_utf16()).collect()
}

/// Converts a path to UTF-16 from UTF-8.  Prepend `prefix`.
pub fn to_u16s(prefix: &[u16], buf: &[u8]) -> Result<Vec<u16>, BadPathError> {
    Ok(prefix.iter()
        .map(|&x| x)
        .chain(str::from_utf8(buf).map_err(BadPathError::BadWTF8)?.encode_utf16())
        .collect())
}

fn is_pipe_or_mailslot(buf: &[u8]) -> bool {
    buf.eq_ignore_ascii_case(b"pipe") || buf.eq_ignore_ascii_case(b"mailslot")
}

fn is_globalroot(buf: &[u8]) -> bool {
    buf.eq_ignore_ascii_case(b"globalroot")
}

fn is_redirector(buf: &[u8]) -> bool {
    buf.eq_ignore_ascii_case(b";LanManRedirector") || buf.eq_ignore_ascii_case(b";WebDavRedirector")
}

// Handles local pipes and mailslots
fn do_localspecial<T, U>(buf: &[u8], off: usize, cb: T) -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{
    let mut q = to_u16s(&[], buf)?;
    q[..4].copy_from_slice(&VERB_PREFIX_16);
    if q.len() > off {
        q[off] = b'\\'.into();
    }
    Ok(cb(&mut q))
}

// Local devices
fn do_localdevice<T, U>(buf: &[u8], cb: T) -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{
    do_conv(&VERB_PREFIX_16, &to_u16s(&[], buf)?[4..], cb)
}

/// Represents errors that can appear when converting a path.
#[derive(Debug)]
pub enum BadPathError {
    /// A UNC path has an empty server.  This means that there are too many
    /// leading slashes in the path.
    EmptyServer,
    /// A UNC path has an empty share.  This usually means that the path has
    /// the form `\\server\\share\something` instead of `\\server\share\something`.
    EmptyShare,
    /// A local-device path has the share `GLOBALROOT` (case-insensitive).  As
    /// this points to the root of the NT Object Manager one cannot safely
    /// canonicalize such a path.  Use a verbatim prefix (`\\?\` or `\??\`) to
    /// access such a path.
    UseVerbatimForGlobalRoot,
    /// The path is invalid WTF-8.  Such paths cannot be safely converted into
    /// Windows paths, which are UCS-2.  Currently, this is emitted if the path
    /// is not valid UTF-8, which is a stricter check.
    BadWTF8(str::Utf8Error),
    /// The path has an embedded NUL character.  This is allowed by the native
    /// NT API, but not by the Windows API.  Currently, Rust uses the Windows
    /// API, so such paths aren’t supported.
    EmbeddedNUL,
    /// The path has too many leading slashes.  A maximum of 2 are allowed.
    TooManyLeadingSlashes,
    /// An I/O error occurred in the Windows API function `GetFullPathNameW`.
    IoError(io::Error),
}


fn handle_unc_path<T, U>(buf: &[u8], cb: T) -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{
    let do_unc = |_, _| unimplemented!();
    let do_redir = |_, _| unimplemented!();
    let res: Result<U, BadPathError> = match parse_two_comps(&buf[2..]) {
        Some((srv, share)) => {
            if share.is_empty() {
                Err(BadPathError::EmptyShare)
            } else if srv == b"." {
                if is_pipe_or_mailslot(share) {
                    do_localspecial(buf, 4 + share.len(), cb)
                } else if is_globalroot(share) {
                    Err(BadPathError::UseVerbatimForGlobalRoot)
                } else {
                    do_localdevice(buf, cb)
                }
            } else if is_redirector(srv) {
                match parse_two_comps(&buf[3 + srv.len()..]) {
                    Some((srv, share)) => {
                        if share.is_empty() {
                            Err(BadPathError::EmptyShare)
                        } else if is_pipe_or_mailslot(share) {
                            do_special(buf, 25, 26 + srv.len(), 27 + srv.len() + share.len(), cb)
                        } else {
                            do_redir(buf, cb)
                        }
                    }
                    None => Err(BadPathError::EmptyServer),
                }
            } else if srv.is_empty() {
                Err(BadPathError::EmptyServer)
            } else if is_pipe_or_mailslot(share) {
                do_special(buf, 7, 8 + srv.len(), 9 + srv.len() + share.len(), cb)
            } else {
                do_unc(buf, cb)
            }
        }
        None => do_localspecial(buf, usize::max_value(), cb),
    };
    res
}

/// Converts a path to a form that will not be corrupted during Windows path conversion.
///
/// # Examples
///
/// A simple mailslot path
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\mailslot\/gamma\").unwrap();
/// win_path::convert(br"\/.\mailslot//gamma\", |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// A simple named pipe path
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\pipe\/alpha").unwrap();
/// win_path::convert(b"//./pipe//alpha", |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// We correctly handle `.` and `..` in named pipe and mailslot path names.
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\pipe\/alpha\..\beta").unwrap();
/// win_path::convert(br"//./pipe//alpha\..\beta", |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// Named pipe and mailslot detection is case-insensitive
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\piPe\/alpha\..\beta").unwrap();
/// win_path::convert(br"//./piPe//alpha\..\beta", |x|assert_eq!(x, res)).unwrap();
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\mailSlot\/gamma\").unwrap();
/// win_path::convert(br"\/.\mailSlot//gamma\", |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// `;LanManRedirector` and `;WebDavRedirector` are properly handled
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\UNC\;LanManRedirector\localhost\pipe\../alpha\..\beta ").unwrap();
/// win_path::convert(br"//;LanManRedirector/localhost\pipe/../alpha\..\beta ",
///                   |x|assert_eq!(x, res)).unwrap();
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\UNC\;WebDavRedirector\localhost\pipe\../alpha\..\beta ").unwrap();
/// win_path::convert(br"//;WebDavRedirector/localhost\pipe/../alpha\..\beta ",
///                   |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// And this is case-insensitive too:
///
/// ```rust
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\UNC\;lANmANRedirector\localhost\pipe\../alpha\..\beta ").unwrap();
/// win_path::convert(br"//;lANmANRedirector/localhost\pipe/../alpha\..\beta ",
///                   |x|assert_eq!(x, res)).unwrap();
/// let res: &[u16] = &win_path::to_u16s(&[], br"\\?\UNC\;wEBdAVRedirector\localhost\pipe\../alpha\..\beta ").unwrap();
/// win_path::convert(br"//;wEBdAVRedirector/localhost\pipe/../alpha\..\beta ",
///                   |x|assert_eq!(x, res)).unwrap()
/// ```
///
/// Verbatim paths are preserved unchanged.  Both `\\?\` and `\??\` are considered
/// to begin a verbatim path:
///
/// ```rust
/// let res = &mut win_path::to_u16s(&[], br"\??\C:/alpha\..").unwrap();
/// win_path::convert(br"\??\C:/alpha\..", |x|assert_eq!(x, res.as_slice())).unwrap();
/// res[1] = b'\\' as u16;
/// win_path::convert(br"\\?\C:/alpha\..", |x|assert_eq!(x, res.as_slice())).unwrap()
/// ```
/// let res: &[u16] = &to_u16s(&[], $out).unwrap();
///
/// `\\.\GLOBALROOT` is rejected — use `\\?\GLOBALROOT` or `\??\GLOBALROOT` if
/// you want this.
///
/// ```rust
/// for &i in &[br"\/./GLoBALrOOT\anything", br"\\.\GLOBALROOT\anything"] {
///     match win_path::convert(i, |_| (unreachable!())) {
///         Err(win_path::BadPathError::UseVerbatimForGlobalRoot) => println!("success!"),
///         _ => unreachable!(),
///     }
/// }
/// ```
pub fn convert<T, U>(buf: &[u8], cb: T) -> Result<U, BadPathError>
    where T: FnOnce(&mut [u16]) -> U
{

    // Check for verbatim paths
    if buf.len() >= 4 {
        match &buf[..4] {
            br"\??\" | br"\\?\" => {
                let mut q = to_u16s(&[], buf)?;
                return Ok(cb(&mut q));
            }
            _ => (),
        }
    }

    match num_slashes(buf) {
        0 | 1 => {
            // Non-UNC paths
            let mut buf = to_u16s(&[], buf)?;
            buf.push(b'\\'.into());
            buf.push(b'a'.into());
            do_conv(&VERB_PREFIX_16, &mut buf, cb)
        }
        2 => handle_unc_path(buf, cb),
        3 => {
            // Error
            Err(BadPathError::TooManyLeadingSlashes)
        }
        _ => unreachable!(),
    }
}


// Many Windows APIs follow a pattern of where we hand a buffer and then they
// will report back to us how large the buffer should be or how many bytes
// currently reside in the buffer. This function is an abstraction over these
// functions by making them easier to call.
//
// The first callback, `f1`, is yielded a (pointer, len) pair which can be
// passed to a syscall. The `ptr` is valid for `len` items (u16 in this case).
// The closure is expected to return what the syscall returns which will be
// interpreted by this function to determine if the syscall needs to be invoked
// again (with more buffer space).
//
// Once the syscall has completed (errors bail out early) the second closure is
// yielded the data which has been read from the syscall. The return value
// from this closure is then the return value of the function.
fn fill_utf16_buf_with_prefix<F1, F2, T>(prefix: &[u16], mut f1: F1, f2: F2) -> io::Result<T>
    where F1: FnMut(*mut u16, c::DWORD) -> c::DWORD,
          F2: FnOnce(&mut [u16]) -> T
{
    // Start off with a stack buf but then spill over to the heap if we end up
    // needing more space.
    let mut stack_buf = [0u16; 512];
    let mut heap_buf = Vec::new();
    unsafe {
        let mut n = stack_buf.len() - prefix.len();
        loop {
            let buf = if n <= stack_buf.len() - prefix.len() {
                &mut stack_buf[..]
            } else {
                let extra = n - heap_buf.len() + prefix.len();
                heap_buf.reserve(extra);
                heap_buf.set_len(n);
                heap_buf[..prefix.len()].copy_from_slice(prefix);
                &mut heap_buf[..]
            };

            // This function is typically called on windows API functions which
            // will return the correct length of the string, but these functions
            // also return the `0` on error. In some cases, however, the
            // returned "correct length" may actually be 0!
            //
            // To handle this case we call `SetLastError` to reset it to 0 and
            // then check it again if we get the "0 error value". If the "last
            // error" is still 0 then we interpret it as a 0 length buffer and
            // not an actual error.
            c::SetLastError(0);
            assert!(prefix.len() <= buf.len());
            let k = match f1(buf.as_mut_ptr().offset(prefix.len() as isize),
                             n as c::DWORD) {
                0 if c::GetLastError() == 0 => 0,
                0 => return Err(io::Error::last_os_error()),
                n => n,
            } as usize;
            if k == n && c::GetLastError() == c::ERROR_INSUFFICIENT_BUFFER {
                n = n * 3 / 2;
            } else if k >= n {
                n = k;
            } else {
                return Ok(f2(&mut buf[..k]));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn no_slashes() {
        assert_eq!(num_slashes(br"C:\gamma"), 0);
    }
    #[test]
    fn two_backslashes() {
        assert_eq!(num_slashes(br"\\?\pipe\alpha"), 2);
    }
    #[test]
    fn one_backslash() {
        assert_eq!(num_slashes(br"\?\pipe\alpha"), 1);
    }
    #[test]
    fn one_slash() {
        assert_eq!(num_slashes(br"/?\pipe\alpha"), 1);
    }
    #[test]
    fn backslash_slash() {
        assert_eq!(num_slashes(br"\/?\pipe\alpha"), 2);
    }
    #[test]
    fn bss() {
        assert_eq!(num_slashes(br"\/?\pipe\alpha"), 2);
    }
    #[test]
    fn too_many_slashes() {
        assert_eq!(num_slashes(br"\//\pipe\alpha"), 3);
    }
    macro_rules! my_test {
        ($name: ident, $input: expr, $out: expr) => {
            #[test]
            fn $name() {
                let res: &[u16] = &to_u16s(&[], $out).unwrap();
                convert($input, |x|assert_eq!(x, res)).unwrap()
            }
        }
    }
    my_test!(simple_pipe, b"//./pipe//alpha", br"\\?\pipe\/alpha");
    my_test!(simple_mailslot,
             br"\/.\mailSlot//gamma\",
             br"\\?\mailSlot\/gamma\");
    my_test!(redirector,
             br"/\;lanManredirector/alpha/pipe//\a ",
             br"\\?\UNC\;lanManredirector\alpha\pipe\/\a ");
    my_test!(webdav_redirector,
             br"/\;WebDavRedirector/alpha/pipe//\a ",
             br"\\?\UNC\;WebDavRedirector\alpha\pipe\/\a ");

}
