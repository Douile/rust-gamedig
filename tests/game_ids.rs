#![cfg(test)]

use std::{collections::HashMap, fs, io::Read};

use gamedig::GAMES;

/// Split a str when characters swap between being digits and not digits.
fn split_on_switch_between_alpha_numeric(text: &str) -> Vec<String> {
    if text.is_empty() {
        return vec![];
    }

    let mut parts = Vec::with_capacity(text.len());
    let mut current = Vec::with_capacity(text.len());

    let mut iter = text.chars();
    let c = iter.next().unwrap();
    let mut last_was_numeric = c.is_ascii_digit();
    current.push(c);

    for c in iter {
        if c.is_ascii_digit() == last_was_numeric {
            current.push(c);
        } else {
            parts.push(current.iter().collect());
            current.clear();
            current.push(c);
            last_was_numeric = !last_was_numeric;
        }
    }

    parts.push(current.into_iter().collect());

    parts
}

#[test]
fn split_correctly() {
    assert_eq!(
        split_on_switch_between_alpha_numeric("2D45A"),
        &["2", "D", "45", "A"]
    );
}

#[derive(Clone, Debug)]
pub enum IDRule {
    IDsMustBeLowerCase,
    NumbersAreTheirOwnWord,
    IfFirstWordNumberNoDigits,
    IfLastWordNumberMustBeAppended,
    ConvertRomanNumeralsToArabic,
    TwoWordsOrLessUseFullWords,
    MoreThanTwoWordsMakeAcronym,
    IfIDDuplicateSameGameAppendYearToNewer,
    IfIDDuplicateSameGameAppendProtocol,
    IfIDDuplicateNoAcronym,
    NoDuplicates,
}

#[derive(Clone, Debug)]
pub struct IDFail {
    pub game_id: String,
    pub game_name: String,
    pub expected_id: String,
    pub rule_stack: Vec<IDRule>,
}

impl IDFail {
    fn new(game_id: String, game_name: String, expected_id: String, rule_stack: Vec<IDRule>) -> Self {
        Self {
            game_id,
            game_name,
            expected_id,
            rule_stack,
        }
    }
}

/// Iterate game entries and validate the id matches current rules
pub fn test_game_name_rules<'a, I: Iterator<Item = (&'a str, &'a str)>>(games: I) -> Vec<IDFail> {
    let mut wrong_ids = Vec::with_capacity(games.size_hint().0);

    let mut seen_ids: HashMap<String, Vec<String>> = HashMap::new();

    // We must sort games by year so that rule 3 is applied correctly
    let mut sorted_games: Vec<_> = games
        .map(|(id, game)| {
            // Separate game name into words
            // NOTE: we have to leave "-" in to prevent hyphenated prefixes being parsed as
            // numerals
            let mut optional_game_name_parts = Vec::new();
            // Filter map necessary to move out words
            #[allow(clippy::unnecessary_filter_map)]
            let game_name_words: Vec<_> = game
                .split_inclusive(&[' ', '-'])
                .map(|w| w.trim())
                .filter_map(|w| {
                    if w.starts_with('(') && w.ends_with(')') {
                        optional_game_name_parts.push(w);
                        None
                    } else {
                        Some(w)
                    }
                })
                .map(|w| {
                    w.replace(
                        |c: char| !c.is_ascii_digit() && !c.is_alphabetic() && c != '-',
                        "",
                    )
                })
                .filter(|w| !w.trim_matches('-').is_empty())
                .collect();

            let mut game_year: Option<u16> = None;
            for optional_part in &optional_game_name_parts {
                if let Some(game_year_text) = optional_part
                    .strip_prefix('(')
                    .and_then(|s| s.strip_suffix(')'))
                {
                    if let Ok(year) = game_year_text.parse() {
                        game_year = Some(year);
                        break;
                    }
                }
            }

            (
                id,
                game,
                game_name_words,
                optional_game_name_parts,
                game_year,
            )
        })
        .collect();

    sorted_games.sort_by(|(_, a_name, _, _, a_year), (_, b_name, _, _, b_year)| {
        a_year.cmp(b_year).then(a_name.len().cmp(&b_name.len()))
    });

    let game_count = sorted_games.len();

    for (id, game, mut game_name_words, optional_game_name_parts, game_year) in sorted_games {
        let mut rule_stack = Vec::new();

        let mut suffix = String::new();

        // A game's identification is lowercased only and be created following these
        // rules:
        if id.to_lowercase().ne(id) {
            wrong_ids.push(IDFail::new(
                id.to_owned(),
                game.to_owned(),
                id.to_lowercase(),
                vec![IDRule::IDsMustBeLowerCase],
            ));
        }

        // 5. Roman numbering will be converted to arabic numbering (XIV -> 14).
        game_name_words = {
            let mut is_first = true;
            game_name_words
                .into_iter()
                .map(|w| {
                    // First word will never be a numeral
                    if is_first {
                        is_first = false;
                        w
                    } else if let Ok(number) = roman_numeral::RomanNumeral::from_string(&w) {
                        rule_stack.push(IDRule::ConvertRomanNumeralsToArabic);
                        number.get_u32().to_string()
                    } else {
                        w
                    }
                })
                .collect()
        };

        // 6. Unless numbers are at the end of a name, they will be considered words,
        //    but digits will always be used instead of the acronym (counter to #2)
        //    (Left 4 Dead -> l4d) unless they at the start position (7 Days to Die ->
        //    sdtd), if they are at the end (such as sequel number or the year), always
        //    append them (Team Fortress 2 -> teamfortress2, Unreal Tournament 2003 ->
        //    unrealtournament2003).
        game_name_words = game_name_words
            .into_iter()
            .flat_map(|w| {
                let n = split_on_switch_between_alpha_numeric(&w);
                if n.len() > 1 {
                    rule_stack.push(IDRule::NumbersAreTheirOwnWord);
                }
                n
            })
            .collect();

        // If first word is number make text
        if !game_name_words.is_empty() && game_name_words[0].chars().next().unwrap().is_ascii_digit() {
            game_name_words[0] = number_to_words::number_to_words(game_name_words[0].parse::<f64>().unwrap(), false);
            rule_stack.push(IDRule::IfFirstWordNumberNoDigits);
        }

        // If last word is number append full number
        if let Some(last_word) = game_name_words.last() {
            if last_word.chars().all(|c| c.is_ascii_digit()) {
                suffix += &game_name_words.pop().unwrap();
                rule_stack.push(IDRule::IfLastWordNumberMustBeAppended);
            }
        }

        let main = if game_name_words.len() <= 2 {
            // 1. Names composed of a maximum of two words will result in an id where the
            //    words are concatenated (Dead Cells -> deadcells), acronyms in the name
            //    count as a single word (S.T.A.L.K.E.R. -> stalker).

            rule_stack.push(IDRule::TwoWordsOrLessUseFullWords);

            game_name_words
                .iter()
                .map(|w| w.trim_matches('-').to_owned())
                .collect::<Vec<_>>()
                .join("")
        } else {
            // 2. Names of more than two words shall be made into an acronym made of the
            //    initial letters (The Binding of Isaac -> tboi), hypenation composed words
            //    don't count as a single word, but of how many parts they are made of (Dino
            //    D-Day, 3 words, so ddd).

            rule_stack.push(IDRule::MoreThanTwoWordsMakeAcronym);

            game_name_words
                .iter()
                .map(|w| w.chars().next().unwrap())
                .filter(|c| c.is_alphanumeric())
                .collect()
        };

        // 7. If a game has multiple id entries (by specifying the edition (Minecraft:
        //    Java and Bedrock) or the release version (Counter-Strike 1: 1.5 and 1.6)),
        //    one more entry by the base name (minecraft and counterstrike respectively)
        //    can be added, where it queries in a group said included entries.

        let mut expected_id = format!("{}{}", main, suffix).to_lowercase();

        // 3. If a game has the exact name as a previously existing id's game (Star Wars
        //    Battlefront 2, the 2005 and 2017 one), append the release year to the
        //    newer id (2005 would be swbf2 (suppose we already have this one supported)
        //    and 2017 would be swbf22017).
        if let Some(other_game_name_words) = seen_ids.get(&expected_id) {
            let mut game_names_same = other_game_name_words.len() == game_name_words.len();
            if game_names_same {
                for i in 0 .. game_name_words.len() {
                    if game_name_words[i].to_lowercase() != other_game_name_words[i].to_lowercase() {
                        game_names_same = false;
                        break;
                    }
                }
            }
            if game_names_same {
                if let Some(year) = game_year {
                    rule_stack.push(IDRule::IfIDDuplicateSameGameAppendYearToNewer);
                    expected_id = format!("{}{}", expected_id, year).to_lowercase();
                } else if let Some(protocol) = optional_game_name_parts.first() {
                    // TODO: Needs ID rule
                    rule_stack.push(IDRule::IfIDDuplicateSameGameAppendProtocol);
                    expected_id = format!(
                        "{}{}",
                        expected_id,
                        protocol.trim_matches(|c| c == '(' || c == ')')
                    );
                }
            }
        }

        // 4. If a new id (`Day of Dragons` -> `dod`) results in an id that already
        //    exists (`Day of Defeat` -> `dod`), then the new name should ignore rule #2
        //    (`Day of Dragons` -> `dayofdragons`).
        if seen_ids.contains_key(&expected_id) {
            rule_stack.push(IDRule::IfIDDuplicateNoAcronym);

            let main = game_name_words
                .iter()
                .map(|w| w.trim_matches('-').to_owned())
                .collect::<Vec<_>>()
                .join("");

            expected_id = format!("{}{}", main, suffix).to_lowercase();
        }

        let duplicate = if seen_ids
            .insert(expected_id.clone(), game_name_words)
            .is_some()
        {
            rule_stack.push(IDRule::NoDuplicates);
            true
        } else {
            false
        };

        // Check ID matches
        if id != expected_id || duplicate {
            wrong_ids.push(IDFail::new(
                id.to_owned(),
                game.to_owned(),
                expected_id,
                rule_stack,
            ));
        }
    }

    if !wrong_ids.is_empty() {
        for fail in &wrong_ids {
            println!("{:#?}", fail);
        }
        let percentage = (wrong_ids.len() * 100) / game_count;
        println!(
            "{} ({}%) IDs didn't match naming rules",
            wrong_ids.len(),
            percentage
        );
    }

    wrong_ids
}

#[test]
fn check_definitions_match_name_rules() {
    let wrong = test_game_name_rules(GAMES.entries().map(|(id, game)| (id.to_owned(), game.name)));
    assert!(wrong.is_empty());
}

#[test]
#[ignore = "Don't test node by default"]
fn check_node_definitions_match_name_rules() {
    let mut file = fs::OpenOptions::new()
        .read(true)
        .open("./node-gamedig/games.txt")
        .unwrap();

    let mut text = String::new();
    file.read_to_string(&mut text).unwrap();

    let games = text
        .split('\n')
        .map(|line| line.trim())
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .filter_map(|line| {
            let parts: Vec<_> = line.splitn(3, '|').collect();
            if parts.len() > 1 {
                Some((parts[0].split(',').next().unwrap(), parts[1]))
            } else {
                None
            }
        });

    let wrong = test_game_name_rules(games);
    assert!(wrong.is_empty());
}
