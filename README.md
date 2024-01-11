# Tokyodoves
Tokyodoves is a library of an efficient board of Tokyo Doves
and associated toolkits.
Tokyo Doves is an abstract strategy board game for two players.
See the following pages for its rules.
- A rule book in Japanese:<br>
    <https://image.gamemarket.jp/2019/11/v160.pdf>
- A rule book in English:<br>
    <https://www.daiso-syuppan.com/wp-content/uploads/2021/02/TOKYO-DOVES.pdf>
- A video explaining the rules on YouTube (Japanese):<br>
    <https://www.youtube.com/watch?v=SsyoqnipHWQ>

The board is implemented with the bitboard technique,
which allows for extremely fast operations
including moving, putting and removing pieces.

## Documentation
Documentation is hosted on [docs.rs](https://docs.rs/tokyodoves/)

Alternatively, see [an auto-generated documentation](https://mat-der-d.github.io/tokyodoves/tokyodoves/)
on the repository.

## Features
This crate provides three types of features:
- default (indicate nothing): use only basic entities to play the game
- game: use convenient entities for playing games additionally
- analysis: use tools for analysis and some collections additionally

Note that, if you indicate feature = "analysis", 
your program also uses those that are included when feature = "game".

See the documentation for details.

## Usage

Simply run:

```
cargo add tokyodoves
```

or add an option to select features:

```
cargo add tokyodoves --features analysis
```

Alternatively, add this to your `Cargo.toml`:

```toml
[dependencies]
tokyodoves = "1.0.0"
```

or

```toml
[dependencies]
tokyodoves = { version = "1.0.0", features = ["analysis"] }
```

if you want to use feature "analysis".