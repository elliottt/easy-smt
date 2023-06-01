use crate::sexpr::{Arena, Parser, SExpr};
use std::ffi;
use std::io::{self, BufRead};
use std::process;

pub(crate) struct Solver {
    _handle: process::Child,
    stdin: process::ChildStdin,
    stdout: io::Lines<io::BufReader<process::ChildStdout>>,
    replay_file: Box<dyn io::Write>,
    parser: Parser,
}

impl Solver {
    pub fn new(
        program: ffi::OsString,
        args: Vec<ffi::OsString>,
        replay_file: Box<dyn io::Write>,
    ) -> io::Result<Self> {
        let mut handle = process::Command::new(program)
            .args(args)
            .stdin(process::Stdio::piped())
            .stdout(process::Stdio::piped())
            .spawn()?;
        let stdin = handle.stdin.take().unwrap();
        let stdout = handle.stdout.take().unwrap();

        Ok(Self {
            _handle: handle,
            stdin,
            stdout: io::BufReader::new(stdout).lines(),
            replay_file,
            parser: Parser::new(),
        })
    }

    pub fn send(&mut self, arena: &Arena, expr: SExpr) -> io::Result<()> {
        use io::Write;
        log::trace!("-> {}", arena.display(expr));
        writeln!(self.replay_file, "{}", arena.display(expr))?;
        writeln!(self.stdin, "{}", arena.display(expr))
    }

    pub fn recv(&mut self, arena: &Arena) -> io::Result<SExpr> {
        self.parser.reset();

        for line in self.stdout.by_ref() {
            let line = line?;
            log::trace!("<- {}", line);
            if let Some(res) = self.parser.parse(arena, &line) {
                return Ok(res);
            }
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "Failed to parse solver output",
        ))
    }

    pub fn ack_command(&mut self, arena: &Arena, success: SExpr, c: SExpr) -> io::Result<()> {
        self.send(arena, c)?;
        let resp = self.recv(arena)?;
        if resp == success {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", arena.display(resp)),
            ))
        }
    }
}
