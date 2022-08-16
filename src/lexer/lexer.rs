use crate::{loc::Loc, token::*};

#[derive(Debug, PartialEq, Eq)]
pub struct Lexer<'input> {
    input: &'input [u8],
    line: usize,
    pos: usize,
    next_pos: usize,
    ch: Option<u8>,
}

impl<'input> Lexer<'input> {
    // Lexer のコンストラクター
    pub fn new(input: &'input str) -> Self {
        let input = input.as_bytes();
        let mut l = Self {
            input: input,
            line: 0,
            pos: 0,
            next_pos: 0,
            ch: None,
        };
        l.read_char();
        l
    }

    // 次のトークンを返すメソッド
    // 現在の文字を検査して、次の文字をセットしてから返す
    pub fn next_token(&mut self) -> Token {
        // 空白を読み飛ばす
        self.skip_whitespaces();

        // Tokenを取り出す
        match self.ch {
            None => {
                let kind = TokenKind::EOF;
                let loc = Loc::new(self.line, self.pos, 0);
                Token::new(kind, loc)
            }
            Some(c) => match c {
                // b'/' => {
                //     self.skip_comment();
                //     self.line += 1;
                //     self.next_token()
                // }
                b'\n' => {
                    self.line += 1;
                    self.read_char();
                    self.next_token()
                }
                b'=' => {
                    if let Some(b'=') = self.peek_char() {
                        let kind = TokenKind::EQ;
                        let loc = Loc::new(self.line, self.pos, 2);
                        self.read_char();
                        self.read_char();
                        Token::new(kind, loc)
                    } else {
                        let kind = TokenKind::ASSIGN;
                        let loc = Loc::new(self.line, self.pos, 1);
                        self.read_char();
                        Token::new(kind, loc)
                    }
                }
                b'+' => {
                    let kind = TokenKind::PLUS;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'-' => {
                    let kind = TokenKind::MINUS;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'!' => {
                    if let Some(b'=') = self.peek_char() {
                        let kind = TokenKind::NOT_EQ;
                        let loc = Loc::new(self.line, self.pos, 1);
                        self.read_char();
                        self.read_char();
                        Token::new(kind, loc)
                    } else {
                        let kind = TokenKind::BANG;
                        let loc = Loc::new(self.line, self.pos, 1);
                        self.read_char();
                        Token::new(kind, loc)
                    }
                }
                b'*' => {
                    let kind = TokenKind::ASTERISK;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'/' => {
                    let kind = TokenKind::SLASH;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'<' => {
                    let kind = TokenKind::LT;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }

                b'>' => {
                    let kind = TokenKind::GT;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b',' => {
                    let kind = TokenKind::COMMA;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b';' => {
                    let kind = TokenKind::SEMICOLON;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b':' => {
                    let kind = TokenKind::COLON;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'(' => {
                    let kind = TokenKind::LPAREN;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b')' => {
                    let kind = TokenKind::RPAREN;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'{' => {
                    let kind = TokenKind::LBRACE;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'}' => {
                    let kind = TokenKind::RBRACE;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b'[' => {
                    let kind = TokenKind::LBRACKET;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                b']' => {
                    let kind = TokenKind::RBRACKET;
                    let loc = Loc::new(self.line, self.pos, 1);
                    self.read_char();
                    Token::new(kind, loc)
                }
                _ => {
                    if self.is_digit() {
                        let s = String::from_utf8(self.read_number().to_vec()).unwrap();
                        let n = s.parse::<usize>().unwrap();
                        let kind = TokenKind::INT(n);
                        let loc = Loc::new(self.line, self.pos - s.len(), s.len());
                        Token::new(kind, loc)
                    } else if self.is_letter() {
                        let ident = String::from_utf8(self.read_identifier().to_vec()).unwrap();
                        let width = ident.len();
                        match lookup_keyword(&ident) {
                            Some(kind) => {
                                Token::new(kind, Loc::new(self.line, self.pos - width, width))
                            }
                            None => Token::new(
                                TokenKind::STRING(ident),
                                Loc::new(self.line, self.pos - width, width),
                            ),
                        }
                    } else {
                        Token::new(TokenKind::ILLEGAL, Loc::new(self.line, self.pos, 1))
                    }
                }
            },
        }
    }

    // 次の文字を読み込む
    fn read_char(&mut self) {
        if self.next_pos >= self.input.len() {
            self.ch = None;
        } else {
            self.ch = Some(self.input[self.next_pos]);
        }
        self.pos = self.next_pos;
        self.next_pos += 1;
    }

    // 次の文字を先読み
    fn peek_char(&self) -> Option<u8> {
        if self.next_pos >= self.input.len() {
            return None;
        }

        Some(self.input[self.next_pos])
    }

    //
    fn skip_comment(&mut self) {
        while !self.is_newline() {
            self.read_char();
        }
        self.read_char()
    }

    // 空白を読み飛ばす
    fn skip_whitespaces(&mut self) {
        while self.is_whitespace() {
            self.read_char()
        }
    }

    // Identifierを読み取るメソッド
    fn read_identifier(&mut self) -> &[u8] {
        let pos = self.pos;
        while self.is_letter() || self.is_digit() {
            self.read_char();
        }

        &self.input[pos..self.pos]
    }

    // 数字を読み取るメソッド
    // 負の数字にも対応
    pub fn read_number(&mut self) -> &[u8] {
        let pos = self.pos;
        // 先頭が '-' の時は一文字読み飛ばす
        if self.is_minus_lit() {
            self.read_char();
        }

        while self.is_digit() {
            self.read_char()
        }

        &self.input[pos..self.pos]
    }

    // 空白を判定するメソッド
    fn is_whitespace(&self) -> bool {
        match self.ch {
            None => false,
            Some(c) => c as char == ' ' || c as char == '\t',
        }
    }

    // 改行を判定するメソッド
    fn is_newline(&self) -> bool {
        match self.ch {
            None => false,
            Some(c) => c as char == '\r' || c as char == '\n',
        }
    }

    // 文字を判定するメソッド
    fn is_letter(&self) -> bool {
        match self.ch {
            None => false,
            Some(c) => (b'a' <= c && c <= b'z') || (b'A' <= c && c <= b'Z'),
        }
    }

    // 数字を判定するメソッド
    fn is_digit(&self) -> bool {
        match self.ch {
            None => false,
            Some(c) => b'0' <= c && c <= b'9',
        }
    }

    // '-' を判定するメソッド
    fn is_minus_lit(&mut self) -> bool {
        match self.ch {
            None => false,
            Some(c) => c == b'-',
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;
    // EOF の代わりにNoneを返す
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.input.len() {
            return None;
        }
        Some(self.next_token())
    }
}
