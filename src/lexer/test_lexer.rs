use crate::{lexer::lexer::*, token::TokenKind};

#[test]
fn test_lexer_keywords() {
    let input = "fn let true false if else return";
    let mut l = Lexer::new(input);
    assert_eq!(l.next_token().kind, TokenKind::FUNCITON);
    assert_eq!(l.next_token().kind, TokenKind::LET);
    assert_eq!(l.next_token().kind, TokenKind::TRUE);
    assert_eq!(l.next_token().kind, TokenKind::FALSE);
    assert_eq!(l.next_token().kind, TokenKind::IF);
    assert_eq!(l.next_token().kind, TokenKind::ELSE);
    assert_eq!(l.next_token().kind, TokenKind::RETURN)
}

#[test]
fn test_lexer_operators() {
    let input = "= + - ! * / < > == !=";
    let mut l = Lexer::new(input);
    assert_eq!(l.next_token().kind, TokenKind::ASSIGN);
    assert_eq!(l.next_token().kind, TokenKind::PLUS);
    assert_eq!(l.next_token().kind, TokenKind::MINUS);
    assert_eq!(l.next_token().kind, TokenKind::BANG);
    assert_eq!(l.next_token().kind, TokenKind::ASTERISK);
    assert_eq!(l.next_token().kind, TokenKind::SLASH);
    assert_eq!(l.next_token().kind, TokenKind::LT);
    assert_eq!(l.next_token().kind, TokenKind::GT);
    assert_eq!(l.next_token().kind, TokenKind::EQ);
    assert_eq!(l.next_token().kind, TokenKind::NOT_EQ);
}

#[test]
fn test_lexer_delimitors() {
    let input = ",;: () {} []";
    let mut l = Lexer::new(input);
    assert_eq!(l.next_token().kind, TokenKind::COMMA);
    assert_eq!(l.next_token().kind, TokenKind::SEMICOLON);
    assert_eq!(l.next_token().kind, TokenKind::COLON);
    assert_eq!(l.next_token().kind, TokenKind::LPAREN);
    assert_eq!(l.next_token().kind, TokenKind::RPAREN);
    assert_eq!(l.next_token().kind, TokenKind::LBRACE);
    assert_eq!(l.next_token().kind, TokenKind::RBRACE);
    assert_eq!(l.next_token().kind, TokenKind::LBRACKET);
    assert_eq!(l.next_token().kind, TokenKind::RBRACKET);
}

#[test]
fn test_lexer_identifier() {
    let input = "x b i";
    let mut l = Lexer::new(input);

    let tok = l.next_token();
    assert_eq!(tok.kind, TokenKind::IDENT);
    assert_eq!(tok.val, Some("x".into()));

    let tok = l.next_token();
    assert_eq!(tok.kind, TokenKind::IDENT);
    assert_eq!(tok.val, Some("b".into()));

    let tok = l.next_token();
    assert_eq!(tok.kind, TokenKind::IDENT);
    assert_eq!(tok.val, Some("i".into()))
}
