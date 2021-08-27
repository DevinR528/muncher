use std::cell::Cell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackResult {
    NonBrace,
    Okay,
    BraceUnmatched,
}

impl StackResult {
    pub fn is_ok(self) -> bool { self == StackResult::Okay }
}

#[derive(Debug, Clone)]
pub struct Stack<'a> {
    input: &'a str,
    stack: Vec<char>,
    pos: (usize, usize),
}

impl<'s> Stack<'s> {
    /// Creates a `Stack` to parse braced input making sure matching braces
    /// are found. The `Stack` will not advance `Muncher`s peek or next.
    ///
    /// # Example
    ///
    /// ```
    /// use muncher::{Muncher, Stack};
    ///
    /// let input = "([{}])\n";
    /// let mut stack = Stack::new(input, (0, 0));
    /// ```
    pub fn new(input: &'s str, pos: (usize, usize)) -> Stack<'s> {
        Self { input, stack: Vec::default(), pos }
    }
    /// Eat the token if `input` is an open brace or pop if close
    /// brace is found.
    ///
    /// # Example
    ///
    /// ```
    /// use muncher::{Muncher, Stack};
    ///
    /// let input = "([{}])\n";
    /// let mut stack = Stack::new(input, (0, 0));
    /// for ch in input.chars() {
    ///     stack.eat(ch);
    /// }
    /// assert!(stack.is_matched())
    /// ```
    pub fn eat(&mut self, input: char) -> StackResult {
        match input {
            '{' | '[' | '(' => {
                self.push(input);
                StackResult::Okay
            }
            '}' | ']' | ')' => self.pop(input),
            _ => StackResult::NonBrace,
        }
    }

    /// Internal matcher to verify close brace being popped is a match
    /// for the open brace being removed.
    fn brace_match(&mut self, input: char) -> bool {
        match input {
            '}' => self.stack.last() == Some(&'{'),
            ']' => self.stack.last() == Some(&'['),
            ')' => self.stack.last() == Some(&'('),
            _ => false,
        }
    }

    /// add brace to stack
    fn push(&mut self, ch: char) { self.stack.push(ch); }

    /// When input is a close brace pop calls `brace_match` and if match
    /// removes the last open brace.
    fn pop(&mut self, input: char) -> StackResult {
        if self.stack.last().is_some() && self.brace_match(input) {
            self.stack.pop();
            StackResult::Okay
        } else {
            StackResult::BraceUnmatched
        }
    }

    /// Returns true when all braces have been matched with a closing
    /// brace.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "([{}])\n";
    /// let mut munch = Muncher::new(input);
    /// let mut stack = munch.brace_stack();
    /// for ch in munch.peek_until(|c| c == &'\n') {
    ///     stack.eat(*ch);
    /// }
    /// assert!(stack.is_matched())
    /// ```
    pub fn is_matched(&self) -> bool { self.stack.is_empty() }
}

#[derive(Debug, Clone)]
pub struct Fork<'a> {
    input: &'a [(usize, char)],
    peek: Cell<usize>,
}

impl<'f> Fork<'f> {
    /// Resets the peek count of this `Fork`.
    pub fn reset_peek(&self) { self.peek.set(0); }

    fn adv_peek(&self) -> usize {
        let peek = self.peek.get();
        self.peek.set(peek + 1);
        peek
    }

    /// Peeks the next `char` and increments the peek count.
    pub fn peek(&self) -> Option<&char> {
        self.input.get(self.adv_peek()).map(|(_, c)| c)
    }

    /// Seek forward count number of `char`s and returns them as string.
    pub fn seek(&self, count: usize) -> Option<String> {
        let start = self.peek.get();
        let end = start + count;
        if end >= self.input.len() {
            return None;
        }
        Some(self.input[start..end].iter().map(|(_, c)| c).collect())
    }
}

#[derive(Debug, Clone)]
pub struct Muncher<'a> {
    /// Original input
    text: &'a str,
    /// The chars_indices of the input text
    input: Vec<(usize, char)>,
    /// The next char index to peek
    peek: Cell<usize>,
    /// The next char index to eat
    next: usize,
}

impl<'a> Muncher<'a> {
    /// Creates a new `Muncher` of the given input.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "lexable input";
    /// let munch = Muncher::new(input);
    /// ```
    pub fn new(input: &'a str) -> Self {
        Self {
            text: input,
            input: input.char_indices().collect(),
            peek: Cell::new(0),
            next: 0,
        }
    }

    /// A peekable fork that does not alter the position of
    /// the `Muncher`
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    /// assert_eq!(munch.eat(), Some('a'));
    ///
    /// let fork = munch.fork();
    /// assert_eq!(fork.peek(), Some(&'b'));
    ///
    /// assert_eq!(munch.eat(), Some('b'));
    /// assert_eq!(munch.eat(), Some('c'));
    /// ```
    pub fn fork(&self) -> Fork {
        Fork { input: &self.input[self.next..], peek: Cell::new(0) }
    }

    /// Returns a `Stack` that parses matching braces, making sure every
    /// brace is closed.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    /// let stack = munch.brace_stack();
    /// ```
    pub fn brace_stack(&self) -> Stack {
        Stack::new(&self.text[self.next..], self.cursor_position())
    }

    /// Returns the whole input text as `&str`.
    pub fn text(&self) -> &'a str { self.text }

    /// Returns byte index for given char index, if valid. Otherwise returns input len.
    pub fn position_of_char(&self, char_index: usize) -> usize {
        if let Some((byte_index, _)) = self.input.get(char_index) {
            return *byte_index;
        }

        self.text.len()
    }

    /// The current byte index of `Muncher`, not its peek position.
    pub fn position(&self) -> usize { self.position_of_char(self.next) }

    /// The current char index of `Muncher`, not its peek position.
    pub fn char_position(&self) -> usize { self.next }

    /// Returns true when next counter has exhausted input.
    pub fn is_done(&self) -> bool { self.next >= self.input.len() }

    /// Returns colum and line position, both start at (1, 1).
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    /// munch.eat();
    /// assert_eq!(munch.cursor_position(), (2, 1));
    /// ```
    pub fn cursor_position(&self) -> (usize, usize) {
        let mut ln = 1;
        let mut col = 1;

        for (i, (_, ch)) in self.input.iter().enumerate() {
            if self.next == i {
                break;
            }
            if ch == &'\n' {
                col = 1;
                ln += 1;
            } else if ch == &'\r' {
                continue;
            } else {
                col += 1;
            }
        }
        (col, ln)
    }

    /// Resets `peek` to current `next`.
    pub fn reset_peek(&self) -> usize {
        self.peek.set(self.next);
        self.peek.get()
    }

    /// Increments `peek` by one.
    fn adv_peek(&self) -> usize {
        let inc = self.peek.get();
        self.peek.set(inc + 1);
        inc
    }

    /// Gets the char at `peek` index then increments `peek` by one.
    pub fn peek(&self) -> Option<&char> {
        let res = self.input.get(self.peek.get());
        self.adv_peek();
        res.map(|(_, c)| c)
    }

    /// Peek tokens until given predicate is true.
    /// Resets the peek position every time called.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    ///
    /// let text = munch.peek_until(|ch| ch == &'d').collect::<String>();
    /// assert_eq!(text, "abc");
    /// assert_eq!(munch.eat(), Some('a'));
    /// ```
    pub fn peek_until<P>(&self, mut pred: P) -> impl Iterator<Item = &char>
    where
        P: FnMut(&char) -> bool,
    {
        let char_start = self.reset_peek();
        for (_, ch) in self.input.iter().skip(char_start) {
            if pred(ch) {
                break;
            } else {
                self.peek.set(self.peek.get() + 1);
            }
        }
        let char_end = self.peek.get();
        self.peek.set(char_end);
        self.input.iter().skip(char_start).take(char_end - char_start).map(|(_, c)| c)
    }

    /// Peek tokens until given predicate is true returns start and end (as byte
    /// positions). Resets the peek position every time called.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "pánico en la discoteca";
    /// let mut munch = Muncher::new(input);
    ///
    /// let (start, end) = munch.peek_until_count(|ch| ch == &'d');
    /// assert_eq!(&munch.text()[start..end], "pánico en la ");
    /// assert_eq!(munch.eat(), Some('p'));
    /// ```
    pub fn peek_until_count<P>(&self, mut pred: P) -> (usize, usize)
    where
        P: FnMut(&char) -> bool,
    {
        let byte_start = self.position();
        let char_start = self.reset_peek();
        for (_, ch) in self.input.iter().skip(char_start) {
            if pred(ch) {
                break;
            } else {
                self.peek.set(self.peek.get() + 1);
            }
        }

        let byte_end = self.position_of_char(self.peek.get());
        (byte_start, byte_end)
    }

    /// Peeks tokens until needle is found returns start and end.
    /// Resets the peek position every time called.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    ///
    /// let (start, end) = munch.peek_range_of("d");
    /// assert_eq!(&munch.text()[start..end], "abc");
    /// assert_eq!(munch.eat(), Some('a'));
    /// ```
    pub fn peek_range_of(&self, needle: &str) -> (usize, usize) {
        let byte_start = self.position();
        let char_start = self.reset_peek();
        let split = self.text[char_start..].split(needle).collect::<Vec<_>>();
        let char_end = char_start + split[0].chars().count();
        let byte_end = self.position_of_char(char_end);
        (byte_start, byte_end)
    }

    /// Seek the `peek` cursor the given number of chars.
    ///
    /// Returns `Some(&str)` if `seek` does not run into the end
    /// of the input.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "hello world";
    /// let m = Muncher::new(input);
    /// assert_eq!(m.seek(5), Some("hello"));
    /// ```
    pub fn seek(&self, count: usize) -> Option<&str> {
        let char_start = self.peek.get();
        let byte_start = self.position_of_char(char_start);
        let char_end = char_start + count;
        if char_end > self.input.len() {
            return None;
        }
        self.peek.set(char_end);
        let byte_end = self.position_of_char(char_end);
        Some(&self.text()[byte_start..byte_end])
    }

    /// Eats the next char if not at end of input.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abc";
    /// let mut m = Muncher::new(input);
    /// assert_eq!(m.eat(), Some('a'));
    /// assert_eq!(m.eat(), Some('b'));
    /// assert_eq!(m.eat(), Some('c'));
    /// assert_eq!(m.eat(), None);
    /// assert_eq!(m.eat(), None);
    /// ```
    pub fn eat(&mut self) -> Option<char> {
        let res = self.input.get(self.next).copied();
        self.next += 1;
        self.peek.set(self.next);
        res.map(|(_, c)| c)
    }

    /// Eats next white space if next char is space and returns true.
    pub fn eat_ws(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&' ') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }
    /// Eats next newline if next char is newline and returns true.
    /// This handles both windows and unix line endings.
    pub fn eat_eol(&mut self) -> bool {
        self.reset_peek();
        let next = self.peek();
        if next == Some(&'\n') {
            self.eat().is_some()
        } else if next == Some(&'\r') {
            self.eat();
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `=` and returns true, false if not found.
    pub fn eat_eq(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'=') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `[` and returns true, false if not found.
    pub fn eat_open_brc(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'[') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `]` and returns true, false if not found.
    pub fn eat_close_brc(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&']') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `{` and returns true, false if not found.
    pub fn eat_open_curly(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'{') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `}` and returns true, false if not found.
    pub fn eat_close_curly(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'}') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `(` and returns true, false if not found.
    pub fn eat_open_paren(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'(') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `)` and returns true, false if not found.
    pub fn eat_close_paren(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&')') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `"` and returns true, false if not found.
    pub fn eat_double_quote(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'"') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `'` and returns true, false if not found.
    pub fn eat_single_quote(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'\'') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `,` and returns true, false if not found.
    pub fn eat_comma(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&',') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `#` and returns true, false if not found.
    pub fn eat_hash(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'#') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `+` and returns true, false if not found.
    pub fn eat_plus(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'+') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `-` and returns true, false if not found.
    pub fn eat_minus(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'-') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `:` and returns true, false if not found.
    pub fn eat_colon(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&':') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eats `.` and returns true, false if not found.
    pub fn eat_dot(&mut self) -> bool {
        self.reset_peek();
        if self.peek() == Some(&'.') {
            self.eat().is_some()
        } else {
            self.reset_peek();
            false
        }
    }

    /// Eat tokens until given predicate is true.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    ///
    /// let text = munch.eat_until(|ch| ch == &'d').collect::<String>();
    /// assert_eq!(text, "abc");
    /// assert_eq!(munch.eat(), Some('d'));
    /// ```
    pub fn eat_until<P>(&mut self, mut pred: P) -> impl Iterator<Item = char> + '_
    where
        P: FnMut(&char) -> bool,
    {
        let char_start = self.next;
        for (_, ch) in self.input.iter().skip(char_start) {
            if pred(ch) {
                break;
            } else {
                self.next += 1;
            }
        }
        let diff = self.next - char_start;
        self.peek.set(self.next);

        self.input.iter().skip(char_start).take(diff).map(|(_, c)| c).copied()
    }

    /// Eats tokens until given predicate is true returns start and end.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    ///
    /// let (start, end) = munch.eat_until_count(|ch| ch == &'d');
    /// assert_eq!(&munch.text()[start..end], "abc");
    /// assert_eq!(munch.eat(), Some('d'));
    /// ```
    pub fn eat_until_count<P>(&mut self, mut pred: P) -> (usize, usize)
    where
        P: FnMut(&char) -> bool,
    {
        let byte_start = self.position();
        for (_, ch) in self.input.iter().skip(self.char_position()) {
            if pred(ch) {
                break;
            } else {
                self.next += 1;
            }
        }
        self.peek.set(self.next);

        (byte_start, self.position())
    }

    /// Eat tokens until needle is found returns start and end.
    /// Resets the peek position every time called.
    ///
    /// # Example
    /// ```
    /// use muncher::Muncher;
    ///
    /// let input = "abcde";
    /// let mut munch = Muncher::new(input);
    ///
    /// let (start, end) = munch.eat_range_of("d");
    /// assert_eq!(&munch.text()[start..end], "abc");
    /// assert_eq!(munch.eat(), Some('d'));
    /// ```
    pub fn eat_range_of(&mut self, needle: &str) -> (usize, usize) {
        assert!(self.next < self.input.len());

        self.reset_peek();
        let byte_start = self.position();
        let split = self.text[byte_start..].split(needle).collect::<Vec<_>>();

        let char_end = byte_start + split[0].chars().count();
        self.next = char_end;
        (byte_start, self.position_of_char(char_end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position() {
        let input = "abc\ndef\nghi";
        let mut munch = Muncher::new(input);

        let _ = munch.eat_until(|ch| ch == &'c').collect::<String>();
        munch.eat();

        let (c, l) = munch.cursor_position();
        assert_eq!(c, 4);
        assert_eq!(l, 1);
        let _ = munch.eat_until(|ch| ch == &'g').collect::<String>();

        let (c, l) = munch.cursor_position();
        assert_eq!(c, 1);
        assert_eq!(l, 3);
    }

    #[test]
    fn test_position_codepoints() {
        let input = "ábc\ndeá\ng🍌hi";
        let mut munch = Muncher::new(input);

        let _ = munch.eat_until(|ch| ch == &'c').collect::<String>();
        munch.eat();

        let (c, l) = munch.cursor_position();
        assert_eq!(c, 4);
        assert_eq!(l, 1);
        let _ = munch.eat_until(|ch| ch == &'i').collect::<String>();

        let (c, l) = munch.cursor_position();
        assert_eq!(c, 4);
        assert_eq!(l, 3);
    }

    #[test]
    fn advance_muncher() {
        let input = "hello world";
        let mut m = Muncher::new(input);

        assert_eq!(m.eat(), Some('h'));

        for ch in m.eat_until(|c| c.is_whitespace()) {
            println!("{}", ch);
            assert!(!ch.is_whitespace());
        }
        assert_eq!(m.peek(), Some(&' '));
        assert_eq!(m.eat(), Some(' '));
    }

    #[test]
    fn end_eat_while_muncher() {
        let input = "hello world";
        let mut m = Muncher::new(input);

        assert_eq!(m.eat(), Some('h'));

        for ch in m.eat_until(|c| c.is_whitespace()) {
            assert!(!ch.is_whitespace());
        }
        assert_eq!(m.peek(), Some(&' '));
        assert_eq!(m.eat(), Some(' '));
        for ch in m.eat_until(|c| c.is_whitespace()) {
            assert!(!ch.is_whitespace());
        }
        assert!(m.eat().is_none());
        assert!(m.peek().is_none());
    }

    #[test]
    fn peek_muncher() {
        let input = "hello world";
        let chars = input.to_string().chars().collect::<Vec<char>>();
        let mut m = Muncher::new(input);

        assert_eq!(m.eat(), Some('h'));

        let mut idx = 0;
        while let Some(_ch) = m.eat() {
            idx += 1;
            assert_eq!(m.peek(), chars.get(idx + 1));
        }
    }

    #[test]
    fn peek_count() {
        let input = "abcde";
        let munch = Muncher::new(input);

        let (start, end) = munch.peek_until_count(|ch| ch == &'d');
        assert_eq!(&munch.text()[start..end], "abc");
    }

    #[test]
    fn peek_count_codepoints() {
        let input = "pánico en la discoteca\npánico en la discoteca";
        let mut munch = Muncher::new(input);

        let (start, end) = munch.peek_until_count(|ch| ch == &'d');
        assert_eq!(&munch.text()[start..end], "pánico en la ");

        let (start, end) = munch.eat_until_count(|ch| ch == &'d');
        assert_eq!(&munch.text()[start..end], "pánico en la ");

        assert_eq!(munch.eat(), Some('d'));
        assert_eq!(munch.peek(), Some(&'i'));

        let (start, end) = munch.peek_until_count(|ch| ch == &'d');
        assert_eq!(&munch.text()[start..end], "iscoteca\npánico en la ");
    }

    #[test]
    fn peek_range_of() {
        let input = "abcde";
        let munch = Muncher::new(input);

        let (start, end) = munch.peek_range_of("d");
        assert_eq!(&munch.text()[start..end], "abc");
    }

    #[test]
    fn seek_muncher() {
        let input = "hello world";
        let m = Muncher::new(input);

        assert_eq!(m.seek(5), Some("hello"));
        assert_eq!(m.peek.get(), 5);

        assert_eq!(m.peek(), Some(&' '));
        assert_eq!(m.peek.get(), 6);

        assert_eq!(m.input.get(6), Some(&(6, 'w')));
        assert_eq!(m.input.get(10), Some(&(10, 'd')));

        println!("{:#?}", m);
        assert_eq!(m.seek(5), Some("world"));
        assert!(m.peek().is_none());
    }

    #[test]
    fn seek_muncher_codepoints() {
        let input = "pánico en la";
        let m = Muncher::new(input);

        assert_eq!(m.seek(6), Some("pánico"));
        assert_eq!(m.peek.get(), 6);

        assert_eq!(m.peek(), Some(&' '));
        assert_eq!(m.peek.get(), 7);

        println!("{:#?}", m);
        assert_eq!(m.seek(5), Some("en la"));
        assert!(m.peek().is_none());
    }

    #[test]
    fn test_eat_eol() {
        let input = "hello\nworld";
        let mut m = Muncher::new(input);

        // this will advance the cursor.
        // this may not further allocate?
        let _hello = m.eat_until(|c| c == &'\n').collect::<String>();
        assert_eq!(m.peek(), Some(&'\n'));
        assert!(m.eat_eol());
    }

    #[test]
    fn test_fork() {
        let input = "abcde";
        let mut munch = Muncher::new(input);
        assert_eq!(munch.eat(), Some('a'));

        let fork = munch.fork();
        assert_eq!(fork.peek(), Some(&'b'));
        assert_eq!(munch.eat(), Some('b'));
        assert_eq!(munch.eat(), Some('c'));
    }

    #[test]
    fn test_fork_codepoints() {
        let input = "ábcde";
        let mut munch = Muncher::new(input);
        assert_eq!(munch.eat(), Some('á'));

        let fork = munch.fork();
        assert_eq!(fork.peek(), Some(&'b'));
        assert_eq!(munch.eat(), Some('b'));
        assert_eq!(munch.eat(), Some('c'));
    }

    #[test]
    fn test_stack_math() {
        let input = "((5 + (3 * 10)) / 1)\n";
        let munch = Muncher::new(input);
        let mut stack = munch.brace_stack();

        for ch in munch.peek_until(|c| c == &'\n') {
            stack.eat(*ch).is_ok();
        }
        assert!(stack.is_matched())
    }

    #[test]
    fn test_stack_code() {
        let input = "fn a() { fn b() { x = [ (), () ] } }\n";
        let munch = Muncher::new(input);
        let mut stack = munch.brace_stack();

        for ch in munch.peek_until(|c| c == &'\n') {
            stack.eat(*ch).is_ok();
        }
        assert!(stack.is_matched())
    }
    #[test]
    fn test_stack_fail() {
        let input = "(]\n";
        let munch = Muncher::new(input);
        let mut stack = munch.brace_stack();

        for ch in munch.peek_until(|c| c == &'\n') {
            stack.eat(*ch);
        }
        assert!(!stack.is_matched())
    }

    #[test]
    fn bounds_error_this_panics_if_bounds_wrong() {
        let input = "\u{1b}]8;;http://www.google.com/\u{7}google\u{1b}]8;;\u{7} \u{1b}[33mruma-identifiers\u{1b}[0m \u{1b}[1mhello\u{1b}[0m\n\n\u{1b}[1;34m┄\u{1b}[0m\u{1b}[1;34mtable\u{1b}[0m\n\n• one\n• two\n\n\u{1b}[32m────────────────────\u{1b}[0m\n\u{1b}[34mfn\u{1b}[0m \u{1b}[33mmain\u{1b}[0m() {\n    \u{1b}[32mprintln!\u{1b}[0m(\"\u{1b}[36mhello\u{1b}[0m\");\n}\n\u{1b}[32m────────────────────\u{1b}[0m\n";
        let mut munch = Muncher::new(input);
        let _ = munch.eat_until(|c| *c == '\u{1b}');
        loop {
            if munch.is_done() {
                break;
            } else {
                munch.eat();
                let _ = munch.eat_until(|c| *c == '\u{1b}');
                let _ = munch.seek(3) == Some("[0m");
            }
        }
    }
}
