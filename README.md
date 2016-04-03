# Marxistats

This site collects statistical data from Marxist papers. Its goal is to make the data more accessible and to decouple them from the
methodolgies applied to them.

All the data are present in the html files of this repository. We use [litprog](https://github.com/xekoukou/litprog) to get the data
from the page so that we can use them to generate the charts.

For example let us say that we have found an error in some data. The steps to update the data are as follows:

1. We change the html page that contains the data.
2. We use litprog to update the data in the csv files.

```
litprog -html html_page data > data.csv
```

That is all. The charts will be automatically updated.
