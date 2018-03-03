</
  define p: input$=4;
  define q: input$=5;
  define r: output$=24;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>