var args = process.argv;
args.shift();
args.shift();

var fs = require('fs');
args.forEach(function(file_name, index, array) {
  var file = fs.readFileSync(file_name, "utf8");
  var nfile = file.replace(/%lt/g,"<");
      nfile = nfile.replace(/%gt/g,">");
  fs.writeFileSync(file_name, nfile);

});
  
