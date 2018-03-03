</
  define p: output$=25;
  define q: input$=2;
  define r: output$=26;
  alw((!(p and !q) ) or (alw(!r);next(q)) or alw(!r))
/>