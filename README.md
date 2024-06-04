# Classification of generalized Alexander quandles.

GAQprogram.g is a program that classifies generalized Alexander quandles up to order 127.
This program is part of the results of [A. Higashitani, S. Kamada, J. Kosaka and H. Kurihara, "Classification of generalized Alexander quandles", arXiv:2406.01074](https://arxiv.org/abs/2406.01074).
This program is intended to be used with [gap](https://www.gap-system.org/index.html) version 4.12.2 or higher.
Also, this program requires the [rig](https://github.com/gap-packages/rig) package.
After launching `gap`, you can use it by entering `Read("GAQprogram.g");`.
This program outputs GAQ.csv and GAQ_n.

- GAQ.csv outputs the number of order n generalized Alexander quandles, the number of Alexander quandles, and the number of connected generalized Alexander quandles for each n up to 127.
- GAQ_n outputs a list of generalized Alexander quandles of order n.
