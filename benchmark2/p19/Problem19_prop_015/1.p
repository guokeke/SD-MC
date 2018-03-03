</
  define p: output$=21;
  define q: input$=4;
  define r: output$=24;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>