# A lone object where an array was meant

Real APIs collapse a one-element array into the bare object — the shape PHP
and most XML-to-JSON converters produce. Document 1 below has `tags` as an
object; documents 2 and 3 have it as an array.

```sh
lake exe tatami examples/singleton-collapse/input.json
```

`tags` becomes **one** table of three rows, with `Tags.of_root` on it. The
object is read as the one-element case of the array.

It is only read that way because some document really did hold an array
there. If every document had an object, `tags` stays a reference — inference
never guesses a shape the corpus did not show it.

Two shapes next to it that are *not* this, and are still refused:

| corpus | why |
| --- | --- |
| object here, array of **scalars** there | two unrelated shapes, not a singleton |
| object here, **empty** array there | an empty array says nothing about which |
