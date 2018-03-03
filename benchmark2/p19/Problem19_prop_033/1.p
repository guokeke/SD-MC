</
  define p: input$=1;
  define q: input$=5;
  define r: output$=21;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>