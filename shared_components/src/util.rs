use std::{ collections::HashMap, fs, io::{ self, Read } };

use crate::token::*;

pub fn read_file_without_bom(path: &str) -> io::Result<String> {
    let mut file = fs::File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;

    let content = if buffer.starts_with(&[0xef, 0xbb, 0xbf]) {
        String::from_utf8_lossy(&buffer[3..]).to_string()
    } else {
        String::from_utf8_lossy(&buffer).to_string()
    };

    Ok(content)
}

pub fn create_keywords() -> HashMap<String, TokenKind> {
    let mut keywords = HashMap::new();
    keywords.insert("def".to_string(), TokenKind::Keyword(KeywordKind::Def));
    keywords.insert("global".to_string(), TokenKind::Keyword(KeywordKind::Global));
    keywords.insert("let".to_string(), TokenKind::Keyword(KeywordKind::Let));
    keywords.insert("true".to_string(), TokenKind::Literal(Literal::Boolean));
    keywords.insert("false".to_string(), TokenKind::Literal(Literal::Boolean));
    keywords.insert("type".to_string(), TokenKind::Keyword(KeywordKind::Type));
    keywords.insert("import".to_string(), TokenKind::Keyword(KeywordKind::Import));
    keywords.insert("not".to_string(), TokenKind::Operator(OperatorKind::Not));
    keywords.insert("and".to_string(), TokenKind::Operator(OperatorKind::And));
    keywords.insert("or".to_string(), TokenKind::Operator(OperatorKind::Or));
    keywords.insert("if".to_string(), TokenKind::Keyword(KeywordKind::If));
    keywords.insert("else".to_string(), TokenKind::Keyword(KeywordKind::Else));
    keywords.insert("elif".to_string(), TokenKind::Keyword(KeywordKind::Elif));
    keywords.insert("def".to_string(), TokenKind::Keyword(KeywordKind::Def));
    keywords.insert("while".to_string(), TokenKind::Keyword(KeywordKind::While));
    keywords.insert("for".to_string(), TokenKind::Keyword(KeywordKind::For));
    keywords.insert("in".to_string(), TokenKind::Keyword(KeywordKind::In));
    keywords.insert("with".to_string(), TokenKind::Keyword(KeywordKind::With));
    keywords.insert("return".to_string(), TokenKind::Keyword(KeywordKind::Return));
    keywords.insert("native".to_string(), TokenKind::Keyword(KeywordKind::Native));

    keywords
}
