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
See an auto-generated documentation [here](https://mat-der-d.github.io/tokyodoves/tokyodoves/).

## Usage

Simply run:

```
cargo add tokyodoves
```

Alternatively, add this to your `Cargo.toml`:

```toml
[dependencies]
tokyodoves = "0.1"
```