var fs = require('fs');

var file = fs.readFileSync('code.c',"utf8");
var nfile = file.replace(/%lt/g,"<");
    nfile = nfile.replace(/%gt/g,">");
fs.writeFileSync('code.c',nfile);

