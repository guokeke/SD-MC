</
  define p: input$=2;
  define q: input$=6;
  define r: output$=26;
  
  alw(!(p and !q) or (alw(!r);next q) or alw(!r))
/>
