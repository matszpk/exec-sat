// lib.rs - library to call and/or parse SAT solver output.
//
// cnfgen - Generate the DIMACS CNF formulae from operations
// Copyright (C) 2022  Mateusz Szpakowski
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

use std::ffi::OsStr;
use std::io::{self, Read, BufRead, BufReader};
use std::num::ParseIntError;
use std::panic;
use std::process::{Command, Stdio};
use std::str::FromStr;
use std::thread;

/// Error type.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// Duplicated result
    #[error("Too many results")]
    TooManyResults,
    /// If assigned more than once
    #[error("Variable has been assigned more than once")]
    AssignedMoreThanOnce,
    /// If not all variables has been assigned
    #[error("Not all variables has been assigned")]
    NotAllAreAssigned,
    /// Parse error for integers
    #[error("Parse error: {0}")]
    ParseError(#[from] ParseIntError),
    /// I/O error.
    #[error("IO rttot: {0}")]
    IOError(#[from] io::Error),
    /// No input available
    #[error("No input available from solver")]
    NoInputAvailable,
}

/// Sat solver output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatOutput {
    /// An assignment of variables if instance is satisfiable.
    /// The first variable start from index 1.
    pub assignment: Option<Vec<bool>>,
    /// It have some value if result is determined: true if instance is satisfiable or
    /// false if instance is unsatisfiable. It have no value if result is unknown or not given.
    pub satisfiable: Option<bool>,
}

/// Try to parse SAT solver output. It ignores any lines that are not result or
/// variable assignment.
pub fn parse_sat_output(r: impl BufRead) -> Result<SatOutput, Error> {
    let mut assignments = vec![];
    let mut satisfiable = false;
    let mut have_result = false;
    let mut have_assignments = vec![];
    for line in r.lines() {
        match line {
            Ok(line) => match line.chars().next() {
                Some('s') => {
                    if have_result {
                        return Err(Error::TooManyResults);
                    }
                    let trimmed = line[1..].trim_start();
                    if trimmed.starts_with("UNSAT") {
                        return Ok(SatOutput {
                            assignment: None,
                            satisfiable: Some(false),
                        });
                    } else if trimmed.starts_with("SAT") {
                        satisfiable = true;
                    }
                    have_result = true;
                }
                Some('v') => {
                    let line = &line[1..];
                    line.split_whitespace().try_for_each(|x| {
                        let lit = isize::from_str(x)?;
                        let varlit = lit.checked_abs().unwrap() as usize;
                        if varlit != 0 {
                            let req_size = varlit.checked_add(1).unwrap();
                            // resize to required size.
                            if assignments.len() <= req_size {
                                assignments.resize(req_size, false);
                                have_assignments.resize(req_size, false);
                            }
                            // check if variables already assigned
                            if have_assignments[varlit] {
                                return Err(Error::AssignedMoreThanOnce);
                            }
                            assignments[varlit] = lit > 0;
                            have_assignments[varlit] = true;
                        }
                        Ok::<(), Error>(())
                    })?;
                }
                _ => {}
            },
            Err(err) => {
                return Err(err.into());
            }
        }
    }
    if satisfiable {
        if have_assignments.iter().skip(1).all(|x| *x) {
            // all variables assigned - ok
            Ok(SatOutput {
                assignment: if assignments.is_empty() {
                    None
                } else {
                    Some(assignments)
                },
                satisfiable: Some(true),
            })
        } else {
            Err(Error::NotAllAreAssigned)
        }
    } else {
        Ok(SatOutput {
            assignment: None,
            satisfiable: None,
        })
    }
}

/// Try to call (execute) SAT solver. The input argument should be formulae in CNF format.
pub fn call_sat<S, I, R>(program: S, args: I, mut input: R) -> Result<SatOutput, Error>
where
    S: AsRef<OsStr>,
    I: IntoIterator<Item = S>,
    R: Read + Send + 'static,
{
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()?;
    let mut stdin = child.stdin.take().ok_or(Error::NoInputAvailable)?;
    let join = thread::spawn(move || {
        io::copy(&mut input, &mut stdin)
    });
    let output = child.wait_with_output().expect("Failed to wait child");
    
    let exp_satisiable = if let Some(exit_code) = output.status.code() {
        match exit_code {
            10 => Some(true),
            20 => Some(false),
            _ => None
        }
    } else {
        None
    };
    
    // handle join
    match join.join() {
        Ok(t) => {
            match t {
                Err(err) => {
                    return Err(Error::IOError(err));
                }
                _ => (),
            }
        }
        Err(err) => panic::resume_unwind(err),
    }
    
    if !output.stdout.is_empty() {
        let sat_out = parse_sat_output(BufReader::new(output.stdout.as_slice()))?;
        if sat_out.satisfiable.is_none() {
            // if satisfiability is uknown from stdout output
            Ok(SatOutput {
                assignment: None,
                satisfiable: exp_satisiable,
            })
        } else {
            Ok(sat_out)
        }
    } else {
        Ok(SatOutput {
            assignment: None,
            satisfiable: exp_satisiable,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sat_output() {
        let example = r#"c blabla
c bumbum
s SATISFIABLE
v -2 1 3 -5 4 0
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: Some(vec![false, true, false, true, true, false]),
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
s SATISFIABLE
v -2 1 3 -5 0
c This is end
"#;
        assert_eq!(
            Err("Not all variables has been assigned".to_string()),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
s SATISFIABLE
v -2 1 3 4 -5 -4 0
c This is end
"#;
        assert_eq!(
            Err("Variable has been assigned more than once".to_string()),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
s SATISFIABLE
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: None,
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
sSATISFIABLE
v -2 1 3 -5 4 0
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: Some(vec![false, true, false, true, true, false]),
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbam
s SATISFIABLE
v -2 1 3
v -5 4 0
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: Some(vec![false, true, false, true, true, false]),
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbam
s SATISFIABLE
v-2  
v3
v-5   4 1 0
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: Some(vec![false, true, false, true, true, false]),
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blablaxx
c bumbumxxx
s SATISFIABLE
o my god
v -2 1 3
xxx
v -5 4 0
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: Some(vec![false, true, false, true, true, false]),
                satisfiable: Some(true),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
s UNSATISFIABLE
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: None,
                satisfiable: Some(false),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
s SATISFIABLE
s UNSATISFIABLE
c This is end
"#;
        assert_eq!(
            Err("Too many results".to_string()),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
sUNSATISFIABLE
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: None,
                satisfiable: Some(false),
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: None,
                satisfiable: None,
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );

        let example = r#"c blabla
c bumbum
v -1 -3 4 2
c This is end
"#;
        assert_eq!(
            Ok(SatOutput {
                assignment: None,
                satisfiable: None,
            }),
            parse_sat_output(BufReader::new(example.as_bytes())).map_err(|e| e.to_string())
        );
    }
}
