$(document).ready(function() {

    var converter = new Markdown.Converter();
    Markdown.Extra.init(converter,{"extensions": ["fenced_code_gfm"]});

    $(".markdown").each(function() {
            var md = $(this).text();
            var html = converter.makeHtml(md);
            $(this).empty();
            $(this).append(html);

        });

    $("code.c").each(function(){
      var text = $(this).text().replace(/%lt/g,"<");
      text = text.replace(/%gt/g,">");
      $(this).text(text);
    });
    
    $("code.c").before('<p class="code_toggle">Code:</p>');
    $(".code_toggle").click(function(){$(this).next().toggle()});
    setTimeout(function(){$(".code_toggle").next().toggle();},1);

        hljs.initHighlighting();
        MathJax.Hub.Typeset();
})
