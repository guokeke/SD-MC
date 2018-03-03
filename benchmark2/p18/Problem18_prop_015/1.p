</
  define p: input$=2;
  define q: output$=23;
  define r: output$=21;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>
