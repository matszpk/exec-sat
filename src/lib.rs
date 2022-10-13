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

use std::io::{self, BufRead};
use std::num::ParseIntError;
use std::str::FromStr;

/// Error type.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// Duplicated result
    #[error("Too many results")]
    TooManyResults,
    /// Parse error for integers
    #[error("Parse error: {0}")]
    ParseError(#[from] ParseIntError),
    /// I/O error.
    #[error("IO rttot: {0}")]
    IOError(#[from] io::Error),
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
    let mut vars = vec![];
    let mut satisfiable = false;
    let mut have_result = false;
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
                        let varlit = lit.checked_abs().unwrap();
                        if varlit != 0 {
                            let req_size = varlit.checked_add(1).unwrap() as usize;
                            if vars.len() <= req_size {
                                vars.resize(req_size, false)
                            }
                            vars[varlit as usize] = lit > 0;
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
        Ok(SatOutput {
            assignment: if vars.is_empty() { None } else { Some(vars) },
            satisfiable: Some(true),
        })
    } else {
        Ok(SatOutput {
            assignment: None,
            satisfiable: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

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
